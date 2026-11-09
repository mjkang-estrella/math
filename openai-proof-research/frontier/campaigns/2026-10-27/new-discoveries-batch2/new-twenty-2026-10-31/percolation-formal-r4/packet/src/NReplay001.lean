import NReplay000
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_15491 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,false),(66,false),(92,false)]
theorem der_15491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15491 :=
  CNF.rup_sound cl_15491 [cl_14697,cl_7174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7174 v h) (by intro d hd; cases hd)))
def cl_15492 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,false),(66,false),(92,false)]
theorem der_15492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15492 :=
  CNF.rup_sound cl_15492 [cl_14697,cl_7176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7176 v h) (by intro d hd; cases hd)))
def cl_15493 : CNF.NClause := [(56,false),(64,true),(63,false),(62,false),(65,false),(66,false),(92,false)]
theorem der_15493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15493 :=
  CNF.rup_sound cl_15493 [cl_14697,cl_7178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7178 v h) (by intro d hd; cases hd)))
def cl_15494 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,false),(66,false),(92,false)]
theorem der_15494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15494 :=
  CNF.rup_sound cl_15494 [cl_14697,cl_7180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7180 v h) (by intro d hd; cases hd)))
def cl_15495 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,false),(66,false),(92,false)]
theorem der_15495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15495 :=
  CNF.rup_sound cl_15495 [cl_14697,cl_7182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7182 v h) (by intro d hd; cases hd)))
def cl_15496 : CNF.NClause := [(56,false),(64,true),(62,true),(63,true),(65,false),(66,false),(92,false)]
theorem der_15496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15496 :=
  CNF.rup_sound cl_15496 [cl_14697,cl_7184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7184 v h) (by intro d hd; cases hd)))
def cl_15497 : CNF.NClause := [(56,false),(65,true),(63,false),(64,false),(62,false),(66,false),(92,false)]
theorem der_15497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15497 :=
  CNF.rup_sound cl_15497 [cl_14697,cl_7186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7186 v h) (by intro d hd; cases hd)))
def cl_15498 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,true),(66,false),(92,false)]
theorem der_15498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15498 :=
  CNF.rup_sound cl_15498 [cl_14697,cl_7188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7188 v h) (by intro d hd; cases hd)))
def cl_15499 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,true),(66,false),(92,false)]
theorem der_15499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15499 :=
  CNF.rup_sound cl_15499 [cl_14697,cl_7190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7190 v h) (by intro d hd; cases hd)))
def cl_15500 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,true),(66,false),(92,false)]
theorem der_15500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15500 :=
  CNF.rup_sound cl_15500 [cl_14697,cl_7192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7192 v h) (by intro d hd; cases hd)))
def cl_15501 : CNF.NClause := [(56,false),(64,true),(63,false),(62,false),(65,true),(66,false),(92,false)]
theorem der_15501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15501 :=
  CNF.rup_sound cl_15501 [cl_14697,cl_7194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7194 v h) (by intro d hd; cases hd)))
def cl_15502 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,true),(66,false),(92,false)]
theorem der_15502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15502 :=
  CNF.rup_sound cl_15502 [cl_14697,cl_7196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7196 v h) (by intro d hd; cases hd)))
def cl_15503 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,true),(66,false),(92,false)]
theorem der_15503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15503 :=
  CNF.rup_sound cl_15503 [cl_14697,cl_7198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7198 v h) (by intro d hd; cases hd)))
def cl_15504 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(64,true),(66,false),(92,false)]
theorem der_15504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15504 :=
  CNF.rup_sound cl_15504 [cl_14697,cl_7200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7200 v h) (by intro d hd; cases hd)))
def cl_15505 : CNF.NClause := [(56,false),(66,true),(92,false),(63,false),(65,false),(64,false),(62,false)]
theorem der_15505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15505 :=
  CNF.rup_sound cl_15505 [cl_14697,cl_7202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7202 v h) (by intro d hd; cases hd)))
def cl_15506 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,false),(66,true),(92,false)]
theorem der_15506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15506 :=
  CNF.rup_sound cl_15506 [cl_14697,cl_7204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7204 v h) (by intro d hd; cases hd)))
def cl_15507 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,false),(66,true),(92,false)]
theorem der_15507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15507 :=
  CNF.rup_sound cl_15507 [cl_14697,cl_7206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7206 v h) (by intro d hd; cases hd)))
def cl_15508 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,false),(66,true),(92,false)]
theorem der_15508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15508 :=
  CNF.rup_sound cl_15508 [cl_14697,cl_7208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7208 v h) (by intro d hd; cases hd)))
def cl_15509 : CNF.NClause := [(56,false),(64,true),(63,false),(62,false),(65,false),(66,true),(92,false)]
theorem der_15509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15509 :=
  CNF.rup_sound cl_15509 [cl_14697,cl_7210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7210 v h) (by intro d hd; cases hd)))
def cl_15510 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,false),(66,true),(92,false)]
theorem der_15510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15510 :=
  CNF.rup_sound cl_15510 [cl_14697,cl_7212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7212 v h) (by intro d hd; cases hd)))
def cl_15511 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,false),(66,true),(92,false)]
theorem der_15511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15511 :=
  CNF.rup_sound cl_15511 [cl_14697,cl_7214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7214 v h) (by intro d hd; cases hd)))
def cl_15512 : CNF.NClause := [(56,false),(64,true),(62,true),(63,true),(65,false),(66,true),(92,false)]
theorem der_15512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15512 :=
  CNF.rup_sound cl_15512 [cl_14697,cl_7216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7216 v h) (by intro d hd; cases hd)))
def cl_15513 : CNF.NClause := [(56,false),(65,true),(63,false),(64,false),(62,false),(66,true),(92,false)]
theorem der_15513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15513 :=
  CNF.rup_sound cl_15513 [cl_14697,cl_7218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7218 v h) (by intro d hd; cases hd)))
def cl_15514 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,true),(66,true),(92,false)]
theorem der_15514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15514 :=
  CNF.rup_sound cl_15514 [cl_14697,cl_7220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7220 v h) (by intro d hd; cases hd)))
def cl_15515 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,true),(66,true),(92,false)]
theorem der_15515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15515 :=
  CNF.rup_sound cl_15515 [cl_14697,cl_7222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7222 v h) (by intro d hd; cases hd)))
def cl_15516 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,true),(66,true),(92,false)]
theorem der_15516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15516 :=
  CNF.rup_sound cl_15516 [cl_14697,cl_7224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7224 v h) (by intro d hd; cases hd)))
def cl_15517 : CNF.NClause := [(56,false),(64,true),(63,false),(62,false),(65,true),(66,true),(92,false)]
theorem der_15517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15517 :=
  CNF.rup_sound cl_15517 [cl_14697,cl_7226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7226 v h) (by intro d hd; cases hd)))
def cl_15518 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,true),(66,true),(92,false)]
theorem der_15518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15518 :=
  CNF.rup_sound cl_15518 [cl_14697,cl_7228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7228 v h) (by intro d hd; cases hd)))
def cl_15519 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,true),(66,true),(92,false)]
theorem der_15519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15519 :=
  CNF.rup_sound cl_15519 [cl_14697,cl_7230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7230 v h) (by intro d hd; cases hd)))
def cl_15520 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(64,true),(66,true),(92,false)]
theorem der_15520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15520 :=
  CNF.rup_sound cl_15520 [cl_14697,cl_7232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7232 v h) (by intro d hd; cases hd)))
def cl_15521 : CNF.NClause := [(56,false),(92,true),(63,false),(64,false),(65,false),(62,false),(66,false)]
theorem der_15521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15521 :=
  CNF.rup_sound cl_15521 [cl_14697,cl_7234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7234 v h) (by intro d hd; cases hd)))
def cl_15522 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,false),(66,false),(92,true)]
theorem der_15522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15522 :=
  CNF.rup_sound cl_15522 [cl_14697,cl_7236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7236 v h) (by intro d hd; cases hd)))
def cl_15523 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,false),(66,false),(92,true)]
theorem der_15523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15523 :=
  CNF.rup_sound cl_15523 [cl_14697,cl_7238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7238 v h) (by intro d hd; cases hd)))
def cl_15524 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,false),(66,false),(92,true)]
theorem der_15524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15524 :=
  CNF.rup_sound cl_15524 [cl_14697,cl_7240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7240 v h) (by intro d hd; cases hd)))
def cl_15525 : CNF.NClause := [(56,false),(64,true),(63,false),(62,false),(65,false),(66,false),(92,true)]
theorem der_15525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15525 :=
  CNF.rup_sound cl_15525 [cl_14697,cl_7242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7242 v h) (by intro d hd; cases hd)))
def cl_15526 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,false),(66,false),(92,true)]
theorem der_15526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15526 :=
  CNF.rup_sound cl_15526 [cl_14697,cl_7244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7244 v h) (by intro d hd; cases hd)))
def cl_15527 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,false),(66,false),(92,true)]
theorem der_15527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15527 :=
  CNF.rup_sound cl_15527 [cl_14697,cl_7246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7246 v h) (by intro d hd; cases hd)))
def cl_15528 : CNF.NClause := [(56,false),(64,true),(62,true),(63,true),(65,false),(66,false),(92,true)]
theorem der_15528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15528 :=
  CNF.rup_sound cl_15528 [cl_14697,cl_7248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7248 v h) (by intro d hd; cases hd)))
def cl_15529 : CNF.NClause := [(56,false),(65,true),(63,false),(64,false),(62,false),(66,false),(92,true)]
theorem der_15529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15529 :=
  CNF.rup_sound cl_15529 [cl_14697,cl_7250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7250 v h) (by intro d hd; cases hd)))
def cl_15530 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,true),(66,false),(92,true)]
theorem der_15530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15530 :=
  CNF.rup_sound cl_15530 [cl_14697,cl_7252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7252 v h) (by intro d hd; cases hd)))
def cl_15531 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,true),(66,false),(92,true)]
theorem der_15531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15531 :=
  CNF.rup_sound cl_15531 [cl_14697,cl_7254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7254 v h) (by intro d hd; cases hd)))
def cl_15532 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,true),(66,false),(92,true)]
theorem der_15532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15532 :=
  CNF.rup_sound cl_15532 [cl_14697,cl_7256] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7256 v h) (by intro d hd; cases hd)))
def cl_15533 : CNF.NClause := [(56,false),(64,true),(63,false),(62,false),(65,true),(66,false),(92,true)]
theorem der_15533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15533 :=
  CNF.rup_sound cl_15533 [cl_14697,cl_7258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7258 v h) (by intro d hd; cases hd)))
def cl_15534 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,true),(66,false),(92,true)]
theorem der_15534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15534 :=
  CNF.rup_sound cl_15534 [cl_14697,cl_7260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7260 v h) (by intro d hd; cases hd)))
def cl_15535 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,true),(66,false),(92,true)]
theorem der_15535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15535 :=
  CNF.rup_sound cl_15535 [cl_14697,cl_7262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7262 v h) (by intro d hd; cases hd)))
def cl_15536 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(64,true),(66,false),(92,true)]
theorem der_15536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15536 :=
  CNF.rup_sound cl_15536 [cl_14697,cl_7264] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7264 v h) (by intro d hd; cases hd)))
def cl_15537 : CNF.NClause := [(56,false),(66,true),(62,false),(63,false),(65,false),(64,false),(92,true)]
theorem der_15537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15537 :=
  CNF.rup_sound cl_15537 [cl_14697,cl_7266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7266 v h) (by intro d hd; cases hd)))
def cl_15538 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,false),(66,true),(92,true)]
theorem der_15538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15538 :=
  CNF.rup_sound cl_15538 [cl_14697,cl_7268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7268 v h) (by intro d hd; cases hd)))
def cl_15539 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,false),(66,true),(92,true)]
theorem der_15539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15539 :=
  CNF.rup_sound cl_15539 [cl_14697,cl_7270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7270 v h) (by intro d hd; cases hd)))
def cl_15540 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,false),(66,true),(92,true)]
theorem der_15540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15540 :=
  CNF.rup_sound cl_15540 [cl_14697,cl_7272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7272 v h) (by intro d hd; cases hd)))
def cl_15541 : CNF.NClause := [(56,false),(64,true),(62,false),(63,false),(65,false),(66,true),(92,true)]
theorem der_15541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15541 :=
  CNF.rup_sound cl_15541 [cl_14697,cl_7274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7274 v h) (by intro d hd; cases hd)))
def cl_15542 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,false),(66,true),(92,true)]
theorem der_15542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15542 :=
  CNF.rup_sound cl_15542 [cl_14697,cl_7276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7276 v h) (by intro d hd; cases hd)))
def cl_15543 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,false),(66,true),(92,true)]
theorem der_15543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15543 :=
  CNF.rup_sound cl_15543 [cl_14697,cl_7278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7278 v h) (by intro d hd; cases hd)))
def cl_15544 : CNF.NClause := [(56,false),(64,true),(62,true),(63,true),(65,false),(66,true),(92,true)]
theorem der_15544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15544 :=
  CNF.rup_sound cl_15544 [cl_14697,cl_7280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7280 v h) (by intro d hd; cases hd)))
def cl_15545 : CNF.NClause := [(56,false),(65,true),(62,false),(63,false),(64,false),(66,true),(92,true)]
theorem der_15545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15545 :=
  CNF.rup_sound cl_15545 [cl_14697,cl_7282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7282 v h) (by intro d hd; cases hd)))
def cl_15546 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,true),(66,true),(92,true)]
theorem der_15546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15546 :=
  CNF.rup_sound cl_15546 [cl_14697,cl_7284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7284 v h) (by intro d hd; cases hd)))
def cl_15547 : CNF.NClause := [(56,false),(63,true),(62,false),(64,false),(65,true),(66,true),(92,true)]
theorem der_15547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15547 :=
  CNF.rup_sound cl_15547 [cl_14697,cl_7286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7286 v h) (by intro d hd; cases hd)))
def cl_15548 : CNF.NClause := [(56,false),(63,true),(62,true),(64,false),(65,true),(66,true),(92,true)]
theorem der_15548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15548 :=
  CNF.rup_sound cl_15548 [cl_14697,cl_7288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7288 v h) (by intro d hd; cases hd)))
def cl_15549 : CNF.NClause := [(56,false),(64,true),(62,false),(63,false),(65,true),(66,true),(92,true)]
theorem der_15549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15549 :=
  CNF.rup_sound cl_15549 [cl_14697,cl_7290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7290 v h) (by intro d hd; cases hd)))
def cl_15550 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,true),(66,true),(92,true)]
theorem der_15550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15550 :=
  CNF.rup_sound cl_15550 [cl_14697,cl_7292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7292 v h) (by intro d hd; cases hd)))
def cl_15551 : CNF.NClause := [(56,false),(63,true),(62,false),(64,true),(65,true),(66,true),(92,true)]
theorem der_15551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15551 :=
  CNF.rup_sound cl_15551 [cl_14697,cl_7294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7294 v h) (by intro d hd; cases hd)))
def cl_15552 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(64,true),(66,true),(92,true)]
theorem der_15552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15552 :=
  CNF.rup_sound cl_15552 [cl_14697,cl_7296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7296 v h) (by intro d hd; cases hd)))
def cl_15553 : CNF.NClause := [(61,false),(72,false),(67,false),(62,false),(77,false),(82,false),(87,false)]
theorem der_15553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15553 :=
  CNF.rup_sound cl_15553 [cl_14698,cl_7810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7810 v h) (by intro d hd; cases hd)))
def cl_15554 : CNF.NClause := [(61,false),(82,false),(62,true),(67,false),(72,false),(77,false),(87,false)]
theorem der_15554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15554 :=
  CNF.rup_sound cl_15554 [cl_14698,cl_7812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7812 v h) (by intro d hd; cases hd)))
def cl_15555 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,false),(82,false),(87,false)]
theorem der_15555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15555 :=
  CNF.rup_sound cl_15555 [cl_14698,cl_7814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7814 v h) (by intro d hd; cases hd)))
def cl_15556 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,false),(82,false),(87,false)]
theorem der_15556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15556 :=
  CNF.rup_sound cl_15556 [cl_14698,cl_7816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7816 v h) (by intro d hd; cases hd)))
def cl_15557 : CNF.NClause := [(61,false),(72,true),(67,false),(87,false),(77,false),(62,false),(82,false)]
theorem der_15557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15557 :=
  CNF.rup_sound cl_15557 [cl_14698,cl_7818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7818 v h) (by intro d hd; cases hd)))
def cl_15558 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,false),(82,false),(87,false)]
theorem der_15558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15558 :=
  CNF.rup_sound cl_15558 [cl_14698,cl_7820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7820 v h) (by intro d hd; cases hd)))
def cl_15559 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,false),(82,false),(87,false)]
theorem der_15559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15559 :=
  CNF.rup_sound cl_15559 [cl_14698,cl_7822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7822 v h) (by intro d hd; cases hd)))
def cl_15560 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,false),(82,false),(87,false)]
theorem der_15560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15560 :=
  CNF.rup_sound cl_15560 [cl_14698,cl_7824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7824 v h) (by intro d hd; cases hd)))
def cl_15561 : CNF.NClause := [(61,false),(72,false),(67,false),(62,false),(77,true),(82,false),(87,false)]
theorem der_15561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15561 :=
  CNF.rup_sound cl_15561 [cl_14698,cl_7826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7826 v h) (by intro d hd; cases hd)))
def cl_15562 : CNF.NClause := [(61,false),(72,false),(62,true),(67,false),(77,true),(82,false),(87,false)]
theorem der_15562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15562 :=
  CNF.rup_sound cl_15562 [cl_14698,cl_7828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7828 v h) (by intro d hd; cases hd)))
def cl_15563 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,true),(82,false),(87,false)]
theorem der_15563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15563 :=
  CNF.rup_sound cl_15563 [cl_14698,cl_7830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7830 v h) (by intro d hd; cases hd)))
def cl_15564 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,true),(82,false),(87,false)]
theorem der_15564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15564 :=
  CNF.rup_sound cl_15564 [cl_14698,cl_7832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7832 v h) (by intro d hd; cases hd)))
def cl_15565 : CNF.NClause := [(61,false),(72,true),(67,false),(77,true),(62,false),(82,false),(87,false)]
theorem der_15565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15565 :=
  CNF.rup_sound cl_15565 [cl_14698,cl_7834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7834 v h) (by intro d hd; cases hd)))
def cl_15566 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,true),(82,false),(87,false)]
theorem der_15566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15566 :=
  CNF.rup_sound cl_15566 [cl_14698,cl_7836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7836 v h) (by intro d hd; cases hd)))
def cl_15567 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,true),(82,false),(87,false)]
theorem der_15567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15567 :=
  CNF.rup_sound cl_15567 [cl_14698,cl_7838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7838 v h) (by intro d hd; cases hd)))
def cl_15568 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,true),(82,false),(87,false)]
theorem der_15568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15568 :=
  CNF.rup_sound cl_15568 [cl_14698,cl_7840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7840 v h) (by intro d hd; cases hd)))
def cl_15569 : CNF.NClause := [(61,false),(82,true),(67,false),(62,false),(77,false),(72,false),(87,false)]
theorem der_15569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15569 :=
  CNF.rup_sound cl_15569 [cl_14698,cl_7842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7842 v h) (by intro d hd; cases hd)))
def cl_15570 : CNF.NClause := [(61,false),(82,true),(62,true),(67,false),(72,false),(77,false),(87,false)]
theorem der_15570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15570 :=
  CNF.rup_sound cl_15570 [cl_14698,cl_7844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7844 v h) (by intro d hd; cases hd)))
def cl_15571 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,false),(82,true),(87,false)]
theorem der_15571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15571 :=
  CNF.rup_sound cl_15571 [cl_14698,cl_7846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7846 v h) (by intro d hd; cases hd)))
def cl_15572 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,false),(82,true),(87,false)]
theorem der_15572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15572 :=
  CNF.rup_sound cl_15572 [cl_14698,cl_7848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7848 v h) (by intro d hd; cases hd)))
def cl_15573 : CNF.NClause := [(61,false),(72,true),(67,false),(87,false),(77,false),(82,true),(62,false)]
theorem der_15573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15573 :=
  CNF.rup_sound cl_15573 [cl_14698,cl_7850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7850 v h) (by intro d hd; cases hd)))
def cl_15574 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,false),(82,true),(87,false)]
theorem der_15574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15574 :=
  CNF.rup_sound cl_15574 [cl_14698,cl_7852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7852 v h) (by intro d hd; cases hd)))
def cl_15575 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,false),(82,true),(87,false)]
theorem der_15575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15575 :=
  CNF.rup_sound cl_15575 [cl_14698,cl_7854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7854 v h) (by intro d hd; cases hd)))
def cl_15576 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,false),(82,true),(87,false)]
theorem der_15576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15576 :=
  CNF.rup_sound cl_15576 [cl_14698,cl_7856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7856 v h) (by intro d hd; cases hd)))
def cl_15577 : CNF.NClause := [(61,false),(72,false),(67,false),(62,false),(77,true),(82,true),(87,false)]
theorem der_15577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15577 :=
  CNF.rup_sound cl_15577 [cl_14698,cl_7858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7858 v h) (by intro d hd; cases hd)))
def cl_15578 : CNF.NClause := [(61,false),(72,false),(62,true),(67,false),(77,true),(82,true),(87,false)]
theorem der_15578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15578 :=
  CNF.rup_sound cl_15578 [cl_14698,cl_7860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7860 v h) (by intro d hd; cases hd)))
def cl_15579 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,true),(82,true),(87,false)]
theorem der_15579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15579 :=
  CNF.rup_sound cl_15579 [cl_14698,cl_7862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7862 v h) (by intro d hd; cases hd)))
def cl_15580 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,true),(82,true),(87,false)]
theorem der_15580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15580 :=
  CNF.rup_sound cl_15580 [cl_14698,cl_7864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7864 v h) (by intro d hd; cases hd)))
def cl_15581 : CNF.NClause := [(61,false),(77,true),(67,false),(72,true),(62,false),(82,true),(87,false)]
theorem der_15581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15581 :=
  CNF.rup_sound cl_15581 [cl_14698,cl_7866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7866 v h) (by intro d hd; cases hd)))
def cl_15582 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,true),(82,true),(87,false)]
theorem der_15582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15582 :=
  CNF.rup_sound cl_15582 [cl_14698,cl_7868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7868 v h) (by intro d hd; cases hd)))
def cl_15583 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,true),(82,true),(87,false)]
theorem der_15583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15583 :=
  CNF.rup_sound cl_15583 [cl_14698,cl_7870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7870 v h) (by intro d hd; cases hd)))
def cl_15584 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,true),(82,true),(87,false)]
theorem der_15584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15584 :=
  CNF.rup_sound cl_15584 [cl_14698,cl_7872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7872 v h) (by intro d hd; cases hd)))
def cl_15585 : CNF.NClause := [(61,false),(87,true),(67,false),(62,false),(77,false),(72,false),(82,false)]
theorem der_15585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15585 :=
  CNF.rup_sound cl_15585 [cl_14698,cl_7874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7874 v h) (by intro d hd; cases hd)))
def cl_15586 : CNF.NClause := [(61,false),(82,false),(62,true),(67,false),(72,false),(77,false),(87,true)]
theorem der_15586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15586 :=
  CNF.rup_sound cl_15586 [cl_14698,cl_7876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7876 v h) (by intro d hd; cases hd)))
def cl_15587 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,false),(82,false),(87,true)]
theorem der_15587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15587 :=
  CNF.rup_sound cl_15587 [cl_14698,cl_7878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7878 v h) (by intro d hd; cases hd)))
def cl_15588 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,false),(82,false),(87,true)]
theorem der_15588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15588 :=
  CNF.rup_sound cl_15588 [cl_14698,cl_7880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7880 v h) (by intro d hd; cases hd)))
def cl_15589 : CNF.NClause := [(61,false),(87,true),(67,false),(72,true),(77,false),(62,false),(82,false)]
theorem der_15589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15589 :=
  CNF.rup_sound cl_15589 [cl_14698,cl_7882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7882 v h) (by intro d hd; cases hd)))
def cl_15590 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,false),(82,false),(87,true)]
theorem der_15590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15590 :=
  CNF.rup_sound cl_15590 [cl_14698,cl_7884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7884 v h) (by intro d hd; cases hd)))
def cl_15591 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,false),(82,false),(87,true)]
theorem der_15591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15591 :=
  CNF.rup_sound cl_15591 [cl_14698,cl_7886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7886 v h) (by intro d hd; cases hd)))
def cl_15592 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,false),(82,false),(87,true)]
theorem der_15592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15592 :=
  CNF.rup_sound cl_15592 [cl_14698,cl_7888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7888 v h) (by intro d hd; cases hd)))
def cl_15593 : CNF.NClause := [(61,false),(72,false),(67,false),(62,false),(77,true),(82,false),(87,true)]
theorem der_15593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15593 :=
  CNF.rup_sound cl_15593 [cl_14698,cl_7890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7890 v h) (by intro d hd; cases hd)))
def cl_15594 : CNF.NClause := [(61,false),(72,false),(62,true),(67,false),(77,true),(82,false),(87,true)]
theorem der_15594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15594 :=
  CNF.rup_sound cl_15594 [cl_14698,cl_7892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7892 v h) (by intro d hd; cases hd)))
def cl_15595 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,true),(82,false),(87,true)]
theorem der_15595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15595 :=
  CNF.rup_sound cl_15595 [cl_14698,cl_7894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7894 v h) (by intro d hd; cases hd)))
def cl_15596 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,true),(82,false),(87,true)]
theorem der_15596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15596 :=
  CNF.rup_sound cl_15596 [cl_14698,cl_7896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7896 v h) (by intro d hd; cases hd)))
def cl_15597 : CNF.NClause := [(61,false),(77,true),(67,false),(72,true),(62,false),(82,false),(87,true)]
theorem der_15597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15597 :=
  CNF.rup_sound cl_15597 [cl_14698,cl_7898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7898 v h) (by intro d hd; cases hd)))
def cl_15598 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,true),(82,false),(87,true)]
theorem der_15598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15598 :=
  CNF.rup_sound cl_15598 [cl_14698,cl_7900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7900 v h) (by intro d hd; cases hd)))
def cl_15599 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,true),(82,false),(87,true)]
theorem der_15599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15599 :=
  CNF.rup_sound cl_15599 [cl_14698,cl_7902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7902 v h) (by intro d hd; cases hd)))
def cl_15600 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,true),(82,false),(87,true)]
theorem der_15600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15600 :=
  CNF.rup_sound cl_15600 [cl_14698,cl_7904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7904 v h) (by intro d hd; cases hd)))
def cl_15601 : CNF.NClause := [(61,false),(82,true),(67,false),(62,false),(77,false),(72,false),(87,true)]
theorem der_15601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15601 :=
  CNF.rup_sound cl_15601 [cl_14698,cl_7906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7906 v h) (by intro d hd; cases hd)))
def cl_15602 : CNF.NClause := [(61,false),(82,true),(62,true),(67,false),(72,false),(77,false),(87,true)]
theorem der_15602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15602 :=
  CNF.rup_sound cl_15602 [cl_14698,cl_7908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7908 v h) (by intro d hd; cases hd)))
def cl_15603 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,false),(82,true),(87,true)]
theorem der_15603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15603 :=
  CNF.rup_sound cl_15603 [cl_14698,cl_7910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7910 v h) (by intro d hd; cases hd)))
def cl_15604 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,false),(82,true),(87,true)]
theorem der_15604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15604 :=
  CNF.rup_sound cl_15604 [cl_14698,cl_7912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7912 v h) (by intro d hd; cases hd)))
def cl_15605 : CNF.NClause := [(61,false),(72,true),(62,false),(67,false),(77,false),(82,true),(87,true)]
theorem der_15605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15605 :=
  CNF.rup_sound cl_15605 [cl_14698,cl_7914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7914 v h) (by intro d hd; cases hd)))
def cl_15606 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,false),(82,true),(87,true)]
theorem der_15606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15606 :=
  CNF.rup_sound cl_15606 [cl_14698,cl_7916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7916 v h) (by intro d hd; cases hd)))
def cl_15607 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,false),(82,true),(87,true)]
theorem der_15607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15607 :=
  CNF.rup_sound cl_15607 [cl_14698,cl_7918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7918 v h) (by intro d hd; cases hd)))
def cl_15608 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,false),(82,true),(87,true)]
theorem der_15608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15608 :=
  CNF.rup_sound cl_15608 [cl_14698,cl_7920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7920 v h) (by intro d hd; cases hd)))
def cl_15609 : CNF.NClause := [(61,false),(72,false),(62,false),(67,false),(77,true),(82,true),(87,true)]
theorem der_15609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15609 :=
  CNF.rup_sound cl_15609 [cl_14698,cl_7922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7922 v h) (by intro d hd; cases hd)))
def cl_15610 : CNF.NClause := [(61,false),(72,false),(62,true),(67,false),(77,true),(82,true),(87,true)]
theorem der_15610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15610 :=
  CNF.rup_sound cl_15610 [cl_14698,cl_7924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7924 v h) (by intro d hd; cases hd)))
def cl_15611 : CNF.NClause := [(61,false),(67,true),(62,false),(72,false),(77,true),(82,true),(87,true)]
theorem der_15611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15611 :=
  CNF.rup_sound cl_15611 [cl_14698,cl_7926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7926 v h) (by intro d hd; cases hd)))
def cl_15612 : CNF.NClause := [(61,false),(67,true),(62,true),(72,false),(77,true),(82,true),(87,true)]
theorem der_15612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15612 :=
  CNF.rup_sound cl_15612 [cl_14698,cl_7928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7928 v h) (by intro d hd; cases hd)))
def cl_15613 : CNF.NClause := [(61,false),(72,true),(62,false),(67,false),(77,true),(82,true),(87,true)]
theorem der_15613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15613 :=
  CNF.rup_sound cl_15613 [cl_14698,cl_7930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7930 v h) (by intro d hd; cases hd)))
def cl_15614 : CNF.NClause := [(61,false),(72,true),(62,true),(67,false),(77,true),(82,true),(87,true)]
theorem der_15614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15614 :=
  CNF.rup_sound cl_15614 [cl_14698,cl_7932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7932 v h) (by intro d hd; cases hd)))
def cl_15615 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,true),(82,true),(87,true)]
theorem der_15615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15615 :=
  CNF.rup_sound cl_15615 [cl_14698,cl_7934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7934 v h) (by intro d hd; cases hd)))
def cl_15616 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,true),(82,true),(87,true)]
theorem der_15616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15616 :=
  CNF.rup_sound cl_15616 [cl_14698,cl_7936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_7936 v h) (by intro d hd; cases hd)))
def cl_15617 : CNF.NClause := [(152,true),(153,false),(151,true),(150,true)]
theorem der_15617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15617 :=
  CNF.rup_sound cl_15617 [cl_14701,cl_14704,cl_7969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_7969 v h) (by intro d hd; cases hd))))
def cl_15618 : CNF.NClause := [(152,false),(153,true),(151,true),(150,true)]
theorem der_15618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15618 :=
  CNF.rup_sound cl_15618 [cl_14701,cl_14704,cl_7970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_7970 v h) (by intro d hd; cases hd))))
def cl_15619 : CNF.NClause := [(152,true),(153,true),(150,true),(151,false)]
theorem der_15619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15619 :=
  CNF.rup_sound cl_15619 [cl_14701,cl_14704,cl_7971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_7971 v h) (by intro d hd; cases hd))))
def cl_15620 : CNF.NClause := [(150,false),(152,true),(151,true),(153,true)]
theorem der_15620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15620 :=
  CNF.rup_sound cl_15620 [cl_14701,cl_14704,cl_7972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_7972 v h) (by intro d hd; cases hd))))
def cl_15621 : CNF.NClause := [(148,false),(128,true),(133,true),(143,true),(138,true)]
theorem der_15621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15621 :=
  CNF.rup_sound cl_15621 [cl_14701,cl_7975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7975 v h) (by intro d hd; cases hd)))
def cl_15622 : CNF.NClause := [(128,true),(143,false),(133,true),(138,true),(148,true)]
theorem der_15622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15622 :=
  CNF.rup_sound cl_15622 [cl_14701,cl_7976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7976 v h) (by intro d hd; cases hd)))
def cl_15623 : CNF.NClause := [(138,false),(148,true),(133,true),(143,true),(128,true)]
theorem der_15623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15623 :=
  CNF.rup_sound cl_15623 [cl_14701,cl_7977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7977 v h) (by intro d hd; cases hd)))
def cl_15624 : CNF.NClause := [(128,true),(133,false),(138,true),(143,true),(148,true)]
theorem der_15624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15624 :=
  CNF.rup_sound cl_15624 [cl_14701,cl_7978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7978 v h) (by intro d hd; cases hd)))
def cl_15625 : CNF.NClause := [(148,true),(128,false),(138,true),(133,true),(143,true)]
theorem der_15625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15625 :=
  CNF.rup_sound cl_15625 [cl_14701,cl_7979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7979 v h) (by intro d hd; cases hd)))
def cl_15626 : CNF.NClause := [(146,false),(136,true),(126,true),(131,true),(141,true)]
theorem der_15626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15626 :=
  CNF.rup_sound cl_15626 [cl_14701,cl_7981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7981 v h) (by intro d hd; cases hd)))
def cl_15627 : CNF.NClause := [(141,false),(136,true),(126,true),(131,true),(146,true)]
theorem der_15627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15627 :=
  CNF.rup_sound cl_15627 [cl_14701,cl_7982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7982 v h) (by intro d hd; cases hd)))
def cl_15628 : CNF.NClause := [(136,false),(146,true),(126,true),(141,true),(131,true)]
theorem der_15628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15628 :=
  CNF.rup_sound cl_15628 [cl_14701,cl_7983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7983 v h) (by intro d hd; cases hd)))
def cl_15629 : CNF.NClause := [(131,false),(136,true),(126,true),(141,true),(146,true)]
theorem der_15629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15629 :=
  CNF.rup_sound cl_15629 [cl_14701,cl_7984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7984 v h) (by intro d hd; cases hd)))
def cl_15630 : CNF.NClause := [(126,false),(136,true),(131,true),(141,true),(146,true)]
theorem der_15630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15630 :=
  CNF.rup_sound cl_15630 [cl_14701,cl_7985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7985 v h) (by intro d hd; cases hd)))
def cl_15631 : CNF.NClause := [(147,false),(127,true),(137,true),(132,true),(142,true)]
theorem der_15631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15631 :=
  CNF.rup_sound cl_15631 [cl_14701,cl_7987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7987 v h) (by intro d hd; cases hd)))
def cl_15632 : CNF.NClause := [(142,false),(147,true),(127,true),(132,true),(137,true)]
theorem der_15632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15632 :=
  CNF.rup_sound cl_15632 [cl_14701,cl_7988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7988 v h) (by intro d hd; cases hd)))
def cl_15633 : CNF.NClause := [(137,false),(132,true),(127,true),(142,true),(147,true)]
theorem der_15633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15633 :=
  CNF.rup_sound cl_15633 [cl_14701,cl_7989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7989 v h) (by intro d hd; cases hd)))
def cl_15634 : CNF.NClause := [(132,false),(127,true),(137,true),(142,true),(147,true)]
theorem der_15634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15634 :=
  CNF.rup_sound cl_15634 [cl_14701,cl_7990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7990 v h) (by intro d hd; cases hd)))
def cl_15635 : CNF.NClause := [(127,false),(132,true),(137,true),(142,true),(147,true)]
theorem der_15635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15635 :=
  CNF.rup_sound cl_15635 [cl_14701,cl_7991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7991 v h) (by intro d hd; cases hd)))
def cl_15636 : CNF.NClause := [(145,false),(135,true),(125,true),(130,true),(140,true)]
theorem der_15636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15636 :=
  CNF.rup_sound cl_15636 [cl_14701,cl_7993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7993 v h) (by intro d hd; cases hd)))
def cl_15637 : CNF.NClause := [(135,true),(140,false),(125,true),(130,true),(145,true)]
theorem der_15637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15637 :=
  CNF.rup_sound cl_15637 [cl_14701,cl_7994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7994 v h) (by intro d hd; cases hd)))
def cl_15638 : CNF.NClause := [(135,false),(130,true),(125,true),(140,true),(145,true)]
theorem der_15638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15638 :=
  CNF.rup_sound cl_15638 [cl_14701,cl_7995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7995 v h) (by intro d hd; cases hd)))
def cl_15639 : CNF.NClause := [(130,false),(135,true),(125,true),(140,true),(145,true)]
theorem der_15639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15639 :=
  CNF.rup_sound cl_15639 [cl_14701,cl_7996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7996 v h) (by intro d hd; cases hd)))
def cl_15640 : CNF.NClause := [(125,false),(130,true),(135,true),(140,true),(145,true)]
theorem der_15640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15640 :=
  CNF.rup_sound cl_15640 [cl_14701,cl_7997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_7997 v h) (by intro d hd; cases hd)))
def cl_15641 : CNF.NClause := [(144,true),(146,true),(145,true),(147,true),(148,false)]
theorem der_15641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15641 :=
  CNF.rup_sound cl_15641 [cl_14704,cl_7999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_7999 v h) (by intro d hd; cases hd)))
def cl_15642 : CNF.NClause := [(144,true),(146,true),(145,true),(147,false),(148,true)]
theorem der_15642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15642 :=
  CNF.rup_sound cl_15642 [cl_14704,cl_8000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8000 v h) (by intro d hd; cases hd)))
def cl_15643 : CNF.NClause := [(144,true),(146,false),(145,true),(147,true),(148,true)]
theorem der_15643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15643 :=
  CNF.rup_sound cl_15643 [cl_14704,cl_8001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8001 v h) (by intro d hd; cases hd)))
def cl_15644 : CNF.NClause := [(144,true),(145,false),(146,true),(147,true),(148,true)]
theorem der_15644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15644 :=
  CNF.rup_sound cl_15644 [cl_14704,cl_8002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8002 v h) (by intro d hd; cases hd)))
def cl_15645 : CNF.NClause := [(144,false),(147,true),(146,true),(145,true),(148,true)]
theorem der_15645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15645 :=
  CNF.rup_sound cl_15645 [cl_14704,cl_8003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8003 v h) (by intro d hd; cases hd)))
def cl_15646 : CNF.NClause := [(138,false),(136,true),(134,true),(135,true),(137,true)]
theorem der_15646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15646 :=
  CNF.rup_sound cl_15646 [cl_14704,cl_8029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8029 v h) (by intro d hd; cases hd)))
def cl_15647 : CNF.NClause := [(137,false),(134,true),(136,true),(135,true),(138,true)]
theorem der_15647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15647 :=
  CNF.rup_sound cl_15647 [cl_14704,cl_8030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8030 v h) (by intro d hd; cases hd)))
def cl_15648 : CNF.NClause := [(136,false),(135,true),(134,true),(137,true),(138,true)]
theorem der_15648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15648 :=
  CNF.rup_sound cl_15648 [cl_14704,cl_8031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8031 v h) (by intro d hd; cases hd)))
def cl_15649 : CNF.NClause := [(134,true),(135,false),(136,true),(137,true),(138,true)]
theorem der_15649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15649 :=
  CNF.rup_sound cl_15649 [cl_14704,cl_8032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8032 v h) (by intro d hd; cases hd)))
def cl_15650 : CNF.NClause := [(134,false),(135,true),(136,true),(137,true),(138,true)]
theorem der_15650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15650 :=
  CNF.rup_sound cl_15650 [cl_14704,cl_8033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8033 v h) (by intro d hd; cases hd)))
def cl_15651 : CNF.NClause := [(143,false),(139,true),(140,true),(141,true),(142,true)]
theorem der_15651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15651 :=
  CNF.rup_sound cl_15651 [cl_14704,cl_8059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8059 v h) (by intro d hd; cases hd)))
def cl_15652 : CNF.NClause := [(142,false),(139,true),(141,true),(140,true),(143,true)]
theorem der_15652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15652 :=
  CNF.rup_sound cl_15652 [cl_14704,cl_8060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8060 v h) (by intro d hd; cases hd)))
def cl_15653 : CNF.NClause := [(141,false),(139,true),(140,true),(142,true),(143,true)]
theorem der_15653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15653 :=
  CNF.rup_sound cl_15653 [cl_14704,cl_8061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8061 v h) (by intro d hd; cases hd)))
def cl_15654 : CNF.NClause := [(139,true),(140,false),(141,true),(142,true),(143,true)]
theorem der_15654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15654 :=
  CNF.rup_sound cl_15654 [cl_14704,cl_8062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8062 v h) (by intro d hd; cases hd)))
def cl_15655 : CNF.NClause := [(139,false),(141,true),(140,true),(142,true),(143,true)]
theorem der_15655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15655 :=
  CNF.rup_sound cl_15655 [cl_14704,cl_8063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8063 v h) (by intro d hd; cases hd)))
def cl_15656 : CNF.NClause := [(132,true),(133,false),(129,true),(130,true),(131,true)]
theorem der_15656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15656 :=
  CNF.rup_sound cl_15656 [cl_14704,cl_8089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8089 v h) (by intro d hd; cases hd)))
def cl_15657 : CNF.NClause := [(132,false),(129,true),(131,true),(130,true),(133,true)]
theorem der_15657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15657 :=
  CNF.rup_sound cl_15657 [cl_14704,cl_8090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8090 v h) (by intro d hd; cases hd)))
def cl_15658 : CNF.NClause := [(131,false),(132,true),(129,true),(130,true),(133,true)]
theorem der_15658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15658 :=
  CNF.rup_sound cl_15658 [cl_14704,cl_8091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8091 v h) (by intro d hd; cases hd)))
def cl_15659 : CNF.NClause := [(130,false),(129,true),(131,true),(132,true),(133,true)]
theorem der_15659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15659 :=
  CNF.rup_sound cl_15659 [cl_14704,cl_8092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8092 v h) (by intro d hd; cases hd)))
def cl_15660 : CNF.NClause := [(129,false),(130,true),(131,true),(132,true),(133,true)]
theorem der_15660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15660 :=
  CNF.rup_sound cl_15660 [cl_14704,cl_8093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8093 v h) (by intro d hd; cases hd)))
def cl_15661 : CNF.NClause := [(127,true),(125,true),(126,true),(128,true)]
theorem der_15661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15661 :=
  CNF.rup_sound cl_15661 [cl_14699,cl_14704,cl_8123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14699 v h) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (inp_8123 v h) (by intro d hd; cases hd))))
def cl_15662 : CNF.NClause := [(153,true),(141,true),(133,true),(137,true),(145,true)]
theorem der_15662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15662 :=
  CNF.rup_sound cl_15662 [cl_14699,cl_8129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14699 v h) (hints_cons _ _ _ (inp_8129 v h) (by intro d hd; cases hd)))
def cl_15663 : CNF.NClause := [(147,true),(151,true),(131,true),(138,true),(140,true)]
theorem der_15663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15663 :=
  CNF.rup_sound cl_15663 [cl_14699,cl_8135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14699 v h) (hints_cons _ _ _ (inp_8135 v h) (by intro d hd; cases hd)))
def cl_15664 : CNF.NClause := [(135,true),(132,true),(146,true),(143,true),(152,true)]
theorem der_15664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15664 :=
  CNF.rup_sound cl_15664 [cl_14699,cl_8141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14699 v h) (hints_cons _ _ _ (inp_8141 v h) (by intro d hd; cases hd)))
def cl_15665 : CNF.NClause := [(130,true),(136,true),(142,true),(148,true),(150,true)]
theorem der_15665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15665 :=
  CNF.rup_sound cl_15665 [cl_14699,cl_8147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14699 v h) (hints_cons _ _ _ (inp_8147 v h) (by intro d hd; cases hd)))
def cl_15666 : CNF.NClause := [(144,true),(134,true),(129,true),(139,true)]
theorem der_15666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15666 :=
  CNF.rup_sound cl_15666 [cl_14699,cl_14701,cl_8153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14699 v h) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (inp_8153 v h) (by intro d hd; cases hd))))
def cl_15667 : CNF.NClause := [(925,true),(926,true),(927,true),(928,true)]
theorem der_15667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15667 :=
  CNF.rup_sound cl_15667 [cl_14700,cl_14705,cl_12623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14700 v h) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12623 v h) (by intro d hd; cases hd))))
def cl_15668 : CNF.NClause := [(903,true),(908,true),(918,true),(913,true),(923,true)]
theorem der_15668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15668 :=
  CNF.rup_sound cl_15668 [cl_14700,cl_12624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14700 v h) (hints_cons _ _ _ (inp_12624 v h) (by intro d hd; cases hd)))
def cl_15669 : CNF.NClause := [(911,true),(901,true),(916,true),(906,true),(921,true)]
theorem der_15669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15669 :=
  CNF.rup_sound cl_15669 [cl_14700,cl_12630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14700 v h) (hints_cons _ _ _ (inp_12630 v h) (by intro d hd; cases hd)))
def cl_15670 : CNF.NClause := [(902,true),(907,true),(917,true),(912,true),(922,true)]
theorem der_15670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15670 :=
  CNF.rup_sound cl_15670 [cl_14700,cl_12636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14700 v h) (hints_cons _ _ _ (inp_12636 v h) (by intro d hd; cases hd)))
def cl_15671 : CNF.NClause := [(900,true),(905,true),(915,true),(910,true),(920,true)]
theorem der_15671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15671 :=
  CNF.rup_sound cl_15671 [cl_14700,cl_12642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14700 v h) (hints_cons _ _ _ (inp_12642 v h) (by intro d hd; cases hd)))
def cl_15672 : CNF.NClause := [(919,true),(920,true),(921,true),(922,true),(923,false)]
theorem der_15672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15672 :=
  CNF.rup_sound cl_15672 [cl_14705,cl_12649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12649 v h) (by intro d hd; cases hd)))
def cl_15673 : CNF.NClause := [(919,true),(920,true),(921,true),(922,false),(923,true)]
theorem der_15673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15673 :=
  CNF.rup_sound cl_15673 [cl_14705,cl_12650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12650 v h) (by intro d hd; cases hd)))
def cl_15674 : CNF.NClause := [(919,true),(920,true),(921,false),(922,true),(923,true)]
theorem der_15674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15674 :=
  CNF.rup_sound cl_15674 [cl_14705,cl_12651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12651 v h) (by intro d hd; cases hd)))
def cl_15675 : CNF.NClause := [(919,true),(920,false),(921,true),(922,true),(923,true)]
theorem der_15675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15675 :=
  CNF.rup_sound cl_15675 [cl_14705,cl_12652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12652 v h) (by intro d hd; cases hd)))
def cl_15676 : CNF.NClause := [(920,true),(919,false),(921,true),(922,true),(923,true)]
theorem der_15676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15676 :=
  CNF.rup_sound cl_15676 [cl_14705,cl_12653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12653 v h) (by intro d hd; cases hd)))
def cl_15677 : CNF.NClause := [(912,true),(913,false),(909,true),(910,true),(911,true)]
theorem der_15677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15677 :=
  CNF.rup_sound cl_15677 [cl_14705,cl_12679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12679 v h) (by intro d hd; cases hd)))
def cl_15678 : CNF.NClause := [(912,false),(909,true),(911,true),(910,true),(913,true)]
theorem der_15678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15678 :=
  CNF.rup_sound cl_15678 [cl_14705,cl_12680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12680 v h) (by intro d hd; cases hd)))
def cl_15679 : CNF.NClause := [(911,false),(910,true),(909,true),(912,true),(913,true)]
theorem der_15679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15679 :=
  CNF.rup_sound cl_15679 [cl_14705,cl_12681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12681 v h) (by intro d hd; cases hd)))
def cl_15680 : CNF.NClause := [(910,false),(909,true),(911,true),(912,true),(913,true)]
theorem der_15680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15680 :=
  CNF.rup_sound cl_15680 [cl_14705,cl_12682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12682 v h) (by intro d hd; cases hd)))
def cl_15681 : CNF.NClause := [(909,false),(910,true),(911,true),(912,true),(913,true)]
theorem der_15681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15681 :=
  CNF.rup_sound cl_15681 [cl_14705,cl_12683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12683 v h) (by intro d hd; cases hd)))
def cl_15682 : CNF.NClause := [(916,true),(915,true),(914,true),(917,true),(918,false)]
theorem der_15682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15682 :=
  CNF.rup_sound cl_15682 [cl_14705,cl_12709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12709 v h) (by intro d hd; cases hd)))
def cl_15683 : CNF.NClause := [(916,true),(917,false),(914,true),(915,true),(918,true)]
theorem der_15683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15683 :=
  CNF.rup_sound cl_15683 [cl_14705,cl_12710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12710 v h) (by intro d hd; cases hd)))
def cl_15684 : CNF.NClause := [(914,true),(915,true),(917,true),(916,false),(918,true)]
theorem der_15684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15684 :=
  CNF.rup_sound cl_15684 [cl_14705,cl_12711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12711 v h) (by intro d hd; cases hd)))
def cl_15685 : CNF.NClause := [(915,false),(914,true),(916,true),(917,true),(918,true)]
theorem der_15685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15685 :=
  CNF.rup_sound cl_15685 [cl_14705,cl_12712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12712 v h) (by intro d hd; cases hd)))
def cl_15686 : CNF.NClause := [(914,false),(915,true),(916,true),(917,true),(918,true)]
theorem der_15686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15686 :=
  CNF.rup_sound cl_15686 [cl_14705,cl_12713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12713 v h) (by intro d hd; cases hd)))
def cl_15687 : CNF.NClause := [(907,true),(908,false),(904,true),(905,true),(906,true)]
theorem der_15687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15687 :=
  CNF.rup_sound cl_15687 [cl_14705,cl_12739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12739 v h) (by intro d hd; cases hd)))
def cl_15688 : CNF.NClause := [(907,false),(904,true),(908,true),(905,true),(906,true)]
theorem der_15688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15688 :=
  CNF.rup_sound cl_15688 [cl_14705,cl_12740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12740 v h) (by intro d hd; cases hd)))
def cl_15689 : CNF.NClause := [(906,false),(907,true),(904,true),(905,true),(908,true)]
theorem der_15689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15689 :=
  CNF.rup_sound cl_15689 [cl_14705,cl_12741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12741 v h) (by intro d hd; cases hd)))
def cl_15690 : CNF.NClause := [(905,false),(904,true),(906,true),(907,true),(908,true)]
theorem der_15690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15690 :=
  CNF.rup_sound cl_15690 [cl_14705,cl_12742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12742 v h) (by intro d hd; cases hd)))
def cl_15691 : CNF.NClause := [(904,false),(905,true),(906,true),(907,true),(908,true)]
theorem der_15691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15691 :=
  CNF.rup_sound cl_15691 [cl_14705,cl_12743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12743 v h) (by intro d hd; cases hd)))
def cl_15692 : CNF.NClause := [(902,true),(901,true),(900,true),(903,false)]
theorem der_15692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15692 :=
  CNF.rup_sound cl_15692 [cl_14702,cl_14705,cl_12769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12769 v h) (by intro d hd; cases hd))))
def cl_15693 : CNF.NClause := [(902,false),(900,true),(901,true),(903,true)]
theorem der_15693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15693 :=
  CNF.rup_sound cl_15693 [cl_14702,cl_14705,cl_12770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12770 v h) (by intro d hd; cases hd))))
def cl_15694 : CNF.NClause := [(901,false),(902,true),(900,true),(903,true)]
theorem der_15694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15694 :=
  CNF.rup_sound cl_15694 [cl_14702,cl_14705,cl_12771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12771 v h) (by intro d hd; cases hd))))
def cl_15695 : CNF.NClause := [(902,true),(901,true),(900,false),(903,true)]
theorem der_15695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15695 :=
  CNF.rup_sound cl_15695 [cl_14702,cl_14705,cl_12772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (inp_12772 v h) (by intro d hd; cases hd))))
def cl_15696 : CNF.NClause := [(916,true),(912,true),(908,true),(920,true),(928,false)]
theorem der_15696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15696 :=
  CNF.rup_sound cl_15696 [cl_14702,cl_12774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12774 v h) (by intro d hd; cases hd)))
def cl_15697 : CNF.NClause := [(916,true),(920,false),(908,true),(912,true),(928,true)]
theorem der_15697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15697 :=
  CNF.rup_sound cl_15697 [cl_14702,cl_12775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12775 v h) (by intro d hd; cases hd)))
def cl_15698 : CNF.NClause := [(912,true),(916,false),(908,true),(920,true),(928,true)]
theorem der_15698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15698 :=
  CNF.rup_sound cl_15698 [cl_14702,cl_12776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12776 v h) (by intro d hd; cases hd)))
def cl_15699 : CNF.NClause := [(912,false),(908,true),(916,true),(920,true),(928,true)]
theorem der_15699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15699 :=
  CNF.rup_sound cl_15699 [cl_14702,cl_12777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12777 v h) (by intro d hd; cases hd)))
def cl_15700 : CNF.NClause := [(908,false),(912,true),(916,true),(920,true),(928,true)]
theorem der_15700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15700 :=
  CNF.rup_sound cl_15700 [cl_14702,cl_12778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12778 v h) (by intro d hd; cases hd)))
def cl_15701 : CNF.NClause := [(922,true),(926,false),(906,true),(913,true),(915,true)]
theorem der_15701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15701 :=
  CNF.rup_sound cl_15701 [cl_14702,cl_12780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12780 v h) (by intro d hd; cases hd)))
def cl_15702 : CNF.NClause := [(922,false),(915,true),(906,true),(913,true),(926,true)]
theorem der_15702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15702 :=
  CNF.rup_sound cl_15702 [cl_14702,cl_12781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12781 v h) (by intro d hd; cases hd)))
def cl_15703 : CNF.NClause := [(915,false),(913,true),(906,true),(922,true),(926,true)]
theorem der_15703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15703 :=
  CNF.rup_sound cl_15703 [cl_14702,cl_12782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12782 v h) (by intro d hd; cases hd)))
def cl_15704 : CNF.NClause := [(913,false),(906,true),(915,true),(922,true),(926,true)]
theorem der_15704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15704 :=
  CNF.rup_sound cl_15704 [cl_14702,cl_12783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12783 v h) (by intro d hd; cases hd)))
def cl_15705 : CNF.NClause := [(906,false),(913,true),(915,true),(922,true),(926,true)]
theorem der_15705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15705 :=
  CNF.rup_sound cl_15705 [cl_14702,cl_12784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12784 v h) (by intro d hd; cases hd)))
def cl_15706 : CNF.NClause := [(918,true),(910,true),(907,true),(921,true),(927,false)]
theorem der_15706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15706 :=
  CNF.rup_sound cl_15706 [cl_14702,cl_12786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12786 v h) (by intro d hd; cases hd)))
def cl_15707 : CNF.NClause := [(921,false),(907,true),(918,true),(910,true),(927,true)]
theorem der_15707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15707 :=
  CNF.rup_sound cl_15707 [cl_14702,cl_12787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12787 v h) (by intro d hd; cases hd)))
def cl_15708 : CNF.NClause := [(918,false),(910,true),(907,true),(921,true),(927,true)]
theorem der_15708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15708 :=
  CNF.rup_sound cl_15708 [cl_14702,cl_12788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12788 v h) (by intro d hd; cases hd)))
def cl_15709 : CNF.NClause := [(910,false),(907,true),(918,true),(921,true),(927,true)]
theorem der_15709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15709 :=
  CNF.rup_sound cl_15709 [cl_14702,cl_12789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12789 v h) (by intro d hd; cases hd)))
def cl_15710 : CNF.NClause := [(907,false),(910,true),(918,true),(921,true),(927,true)]
theorem der_15710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15710 :=
  CNF.rup_sound cl_15710 [cl_14702,cl_12790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12790 v h) (by intro d hd; cases hd)))
def cl_15711 : CNF.NClause := [(911,true),(905,true),(917,true),(923,true),(925,false)]
theorem der_15711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15711 :=
  CNF.rup_sound cl_15711 [cl_14702,cl_12792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12792 v h) (by intro d hd; cases hd)))
def cl_15712 : CNF.NClause := [(917,true),(905,true),(923,false),(911,true),(925,true)]
theorem der_15712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15712 :=
  CNF.rup_sound cl_15712 [cl_14702,cl_12793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12793 v h) (by intro d hd; cases hd)))
def cl_15713 : CNF.NClause := [(917,false),(911,true),(905,true),(923,true),(925,true)]
theorem der_15713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15713 :=
  CNF.rup_sound cl_15713 [cl_14702,cl_12794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12794 v h) (by intro d hd; cases hd)))
def cl_15714 : CNF.NClause := [(911,false),(905,true),(917,true),(923,true),(925,true)]
theorem der_15714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15714 :=
  CNF.rup_sound cl_15714 [cl_14702,cl_12795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12795 v h) (by intro d hd; cases hd)))
def cl_15715 : CNF.NClause := [(905,false),(911,true),(917,true),(923,true),(925,true)]
theorem der_15715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15715 :=
  CNF.rup_sound cl_15715 [cl_14702,cl_12796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (inp_12796 v h) (by intro d hd; cases hd)))
def cl_15716 : CNF.NClause := [(909,true),(904,true),(914,true),(919,true)]
theorem der_15716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15716 :=
  CNF.rup_sound cl_15716 [cl_14702,cl_14700,cl_12798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (der_14700 v h) (hints_cons _ _ _ (inp_12798 v h) (by intro d hd; cases hd))))
def cl_15717 : CNF.NClause := [(1080,true),(1081,true),(1082,true),(1083,true)]
theorem der_15717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15717 :=
  CNF.rup_sound cl_15717 [cl_14707,cl_14703,cl_13548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (der_14703 v h) (hints_cons _ _ _ (inp_13548 v h) (by intro d hd; cases hd))))
def cl_15718 : CNF.NClause := [(1078,false),(1068,true),(1058,true),(1073,true),(1063,true)]
theorem der_15718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15718 :=
  CNF.rup_sound cl_15718 [cl_14707,cl_13555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13555 v h) (by intro d hd; cases hd)))
def cl_15719 : CNF.NClause := [(1058,true),(1063,true),(1068,true),(1073,false),(1078,true)]
theorem der_15719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15719 :=
  CNF.rup_sound cl_15719 [cl_14707,cl_13556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13556 v h) (by intro d hd; cases hd)))
def cl_15720 : CNF.NClause := [(1068,false),(1058,true),(1063,true),(1073,true),(1078,true)]
theorem der_15720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15720 :=
  CNF.rup_sound cl_15720 [cl_14707,cl_13557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13557 v h) (by intro d hd; cases hd)))
def cl_15721 : CNF.NClause := [(1058,true),(1063,false),(1068,true),(1073,true),(1078,true)]
theorem der_15721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15721 :=
  CNF.rup_sound cl_15721 [cl_14707,cl_13558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13558 v h) (by intro d hd; cases hd)))
def cl_15722 : CNF.NClause := [(1058,false),(1063,true),(1068,true),(1073,true),(1078,true)]
theorem der_15722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15722 :=
  CNF.rup_sound cl_15722 [cl_14707,cl_13559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13559 v h) (by intro d hd; cases hd)))
def cl_15723 : CNF.NClause := [(1071,true),(1066,true),(1056,true),(1061,true),(1076,false)]
theorem der_15723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15723 :=
  CNF.rup_sound cl_15723 [cl_14707,cl_13561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13561 v h) (by intro d hd; cases hd)))
def cl_15724 : CNF.NClause := [(1071,false),(1066,true),(1056,true),(1061,true),(1076,true)]
theorem der_15724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15724 :=
  CNF.rup_sound cl_15724 [cl_14707,cl_13562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13562 v h) (by intro d hd; cases hd)))
def cl_15725 : CNF.NClause := [(1066,false),(1056,true),(1061,true),(1071,true),(1076,true)]
theorem der_15725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15725 :=
  CNF.rup_sound cl_15725 [cl_14707,cl_13563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13563 v h) (by intro d hd; cases hd)))
def cl_15726 : CNF.NClause := [(1061,false),(1066,true),(1056,true),(1071,true),(1076,true)]
theorem der_15726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15726 :=
  CNF.rup_sound cl_15726 [cl_14707,cl_13564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13564 v h) (by intro d hd; cases hd)))
def cl_15727 : CNF.NClause := [(1056,false),(1066,true),(1061,true),(1071,true),(1076,true)]
theorem der_15727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15727 :=
  CNF.rup_sound cl_15727 [cl_14707,cl_13565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13565 v h) (by intro d hd; cases hd)))
def cl_15728 : CNF.NClause := [(1072,true),(1067,true),(1057,true),(1062,true),(1077,false)]
theorem der_15728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15728 :=
  CNF.rup_sound cl_15728 [cl_14707,cl_13567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13567 v h) (by intro d hd; cases hd)))
def cl_15729 : CNF.NClause := [(1067,true),(1057,true),(1072,false),(1062,true),(1077,true)]
theorem der_15729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15729 :=
  CNF.rup_sound cl_15729 [cl_14707,cl_13568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13568 v h) (by intro d hd; cases hd)))
def cl_15730 : CNF.NClause := [(1067,false),(1062,true),(1057,true),(1072,true),(1077,true)]
theorem der_15730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15730 :=
  CNF.rup_sound cl_15730 [cl_14707,cl_13569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13569 v h) (by intro d hd; cases hd)))
def cl_15731 : CNF.NClause := [(1062,false),(1057,true),(1067,true),(1072,true),(1077,true)]
theorem der_15731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15731 :=
  CNF.rup_sound cl_15731 [cl_14707,cl_13570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13570 v h) (by intro d hd; cases hd)))
def cl_15732 : CNF.NClause := [(1057,false),(1062,true),(1067,true),(1072,true),(1077,true)]
theorem der_15732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15732 :=
  CNF.rup_sound cl_15732 [cl_14707,cl_13571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13571 v h) (by intro d hd; cases hd)))
def cl_15733 : CNF.NClause := [(1075,false),(1055,true),(1065,true),(1060,true),(1070,true)]
theorem der_15733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15733 :=
  CNF.rup_sound cl_15733 [cl_14707,cl_13573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13573 v h) (by intro d hd; cases hd)))
def cl_15734 : CNF.NClause := [(1070,false),(1065,true),(1055,true),(1060,true),(1075,true)]
theorem der_15734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15734 :=
  CNF.rup_sound cl_15734 [cl_14707,cl_13574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13574 v h) (by intro d hd; cases hd)))
def cl_15735 : CNF.NClause := [(1065,false),(1060,true),(1055,true),(1070,true),(1075,true)]
theorem der_15735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15735 :=
  CNF.rup_sound cl_15735 [cl_14707,cl_13575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13575 v h) (by intro d hd; cases hd)))
def cl_15736 : CNF.NClause := [(1055,true),(1065,true),(1060,false),(1070,true),(1075,true)]
theorem der_15736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15736 :=
  CNF.rup_sound cl_15736 [cl_14707,cl_13576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13576 v h) (by intro d hd; cases hd)))
def cl_15737 : CNF.NClause := [(1055,false),(1060,true),(1065,true),(1070,true),(1075,true)]
theorem der_15737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15737 :=
  CNF.rup_sound cl_15737 [cl_14707,cl_13577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13577 v h) (by intro d hd; cases hd)))
def cl_15738 : CNF.NClause := [(1075,true),(1074,true),(1076,true),(1077,true),(1078,true)]
theorem der_15738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15738 :=
  CNF.rup_sound cl_15738 [cl_14703,cl_13578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14703 v h) (hints_cons _ _ _ (inp_13578 v h) (by intro d hd; cases hd)))
def cl_15739 : CNF.NClause := [(1065,true),(1066,true),(1067,true),(1064,true),(1068,true)]
theorem der_15739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15739 :=
  CNF.rup_sound cl_15739 [cl_14703,cl_13608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14703 v h) (hints_cons _ _ _ (inp_13608 v h) (by intro d hd; cases hd)))
def cl_15740 : CNF.NClause := [(1069,true),(1070,true),(1071,true),(1072,true),(1073,true)]
theorem der_15740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15740 :=
  CNF.rup_sound cl_15740 [cl_14703,cl_13638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14703 v h) (hints_cons _ _ _ (inp_13638 v h) (by intro d hd; cases hd)))
def cl_15741 : CNF.NClause := [(1059,true),(1060,true),(1063,true),(1062,true),(1061,true)]
theorem der_15741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15741 :=
  CNF.rup_sound cl_15741 [cl_14703,cl_13668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14703 v h) (hints_cons _ _ _ (inp_13668 v h) (by intro d hd; cases hd)))
def cl_15742 : CNF.NClause := [(1057,true),(1055,true),(1056,true),(1058,true)]
theorem der_15742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15742 :=
  CNF.rup_sound cl_15742 [cl_14706,cl_14703,cl_13698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (der_14703 v h) (hints_cons _ _ _ (inp_13698 v h) (by intro d hd; cases hd))))
def cl_15743 : CNF.NClause := [(1067,true),(1071,true),(1063,true),(1075,true),(1083,false)]
theorem der_15743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15743 :=
  CNF.rup_sound cl_15743 [cl_14706,cl_13704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13704 v h) (by intro d hd; cases hd)))
def cl_15744 : CNF.NClause := [(1067,true),(1075,false),(1071,true),(1063,true),(1083,true)]
theorem der_15744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15744 :=
  CNF.rup_sound cl_15744 [cl_14706,cl_13705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13705 v h) (by intro d hd; cases hd)))
def cl_15745 : CNF.NClause := [(1067,true),(1071,false),(1063,true),(1075,true),(1083,true)]
theorem der_15745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15745 :=
  CNF.rup_sound cl_15745 [cl_14706,cl_13706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13706 v h) (by intro d hd; cases hd)))
def cl_15746 : CNF.NClause := [(1067,false),(1063,true),(1071,true),(1075,true),(1083,true)]
theorem der_15746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15746 :=
  CNF.rup_sound cl_15746 [cl_14706,cl_13707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13707 v h) (by intro d hd; cases hd)))
def cl_15747 : CNF.NClause := [(1063,false),(1067,true),(1075,true),(1071,true),(1083,true)]
theorem der_15747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15747 :=
  CNF.rup_sound cl_15747 [cl_14706,cl_13708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13708 v h) (by intro d hd; cases hd)))
def cl_15748 : CNF.NClause := [(1068,true),(1061,true),(1070,true),(1077,true),(1081,false)]
theorem der_15748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15748 :=
  CNF.rup_sound cl_15748 [cl_14706,cl_13710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13710 v h) (by intro d hd; cases hd)))
def cl_15749 : CNF.NClause := [(1077,false),(1070,true),(1061,true),(1068,true),(1081,true)]
theorem der_15749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15749 :=
  CNF.rup_sound cl_15749 [cl_14706,cl_13711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13711 v h) (by intro d hd; cases hd)))
def cl_15750 : CNF.NClause := [(1070,false),(1061,true),(1068,true),(1077,true),(1081,true)]
theorem der_15750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15750 :=
  CNF.rup_sound cl_15750 [cl_14706,cl_13712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13712 v h) (by intro d hd; cases hd)))
def cl_15751 : CNF.NClause := [(1061,true),(1068,false),(1077,true),(1070,true),(1081,true)]
theorem der_15751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15751 :=
  CNF.rup_sound cl_15751 [cl_14706,cl_13713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13713 v h) (by intro d hd; cases hd)))
def cl_15752 : CNF.NClause := [(1061,false),(1068,true),(1070,true),(1077,true),(1081,true)]
theorem der_15752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15752 :=
  CNF.rup_sound cl_15752 [cl_14706,cl_13714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13714 v h) (by intro d hd; cases hd)))
def cl_15753 : CNF.NClause := [(1073,true),(1065,true),(1062,true),(1076,true),(1082,false)]
theorem der_15753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15753 :=
  CNF.rup_sound cl_15753 [cl_14706,cl_13716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13716 v h) (by intro d hd; cases hd)))
def cl_15754 : CNF.NClause := [(1065,true),(1076,false),(1062,true),(1073,true),(1082,true)]
theorem der_15754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15754 :=
  CNF.rup_sound cl_15754 [cl_14706,cl_13717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13717 v h) (by intro d hd; cases hd)))
def cl_15755 : CNF.NClause := [(1073,false),(1062,true),(1076,true),(1065,true),(1082,true)]
theorem der_15755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15755 :=
  CNF.rup_sound cl_15755 [cl_14706,cl_13718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13718 v h) (by intro d hd; cases hd)))
def cl_15756 : CNF.NClause := [(1065,false),(1062,true),(1073,true),(1076,true),(1082,true)]
theorem der_15756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15756 :=
  CNF.rup_sound cl_15756 [cl_14706,cl_13719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13719 v h) (by intro d hd; cases hd)))
def cl_15757 : CNF.NClause := [(1062,false),(1065,true),(1073,true),(1076,true),(1082,true)]
theorem der_15757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15757 :=
  CNF.rup_sound cl_15757 [cl_14706,cl_13720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13720 v h) (by intro d hd; cases hd)))
def cl_15758 : CNF.NClause := [(1060,true),(1066,true),(1072,true),(1078,true),(1080,false)]
theorem der_15758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15758 :=
  CNF.rup_sound cl_15758 [cl_14706,cl_13722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13722 v h) (by intro d hd; cases hd)))
def cl_15759 : CNF.NClause := [(1072,true),(1078,false),(1060,true),(1066,true),(1080,true)]
theorem der_15759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15759 :=
  CNF.rup_sound cl_15759 [cl_14706,cl_13723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13723 v h) (by intro d hd; cases hd)))
def cl_15760 : CNF.NClause := [(1072,false),(1060,true),(1066,true),(1078,true),(1080,true)]
theorem der_15760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15760 :=
  CNF.rup_sound cl_15760 [cl_14706,cl_13724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13724 v h) (by intro d hd; cases hd)))
def cl_15761 : CNF.NClause := [(1066,false),(1060,true),(1072,true),(1078,true),(1080,true)]
theorem der_15761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15761 :=
  CNF.rup_sound cl_15761 [cl_14706,cl_13725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13725 v h) (by intro d hd; cases hd)))
def cl_15762 : CNF.NClause := [(1060,false),(1066,true),(1072,true),(1078,true),(1080,true)]
theorem der_15762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15762 :=
  CNF.rup_sound cl_15762 [cl_14706,cl_13726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (inp_13726 v h) (by intro d hd; cases hd)))
def cl_15763 : CNF.NClause := [(1069,true),(1064,true),(1059,true),(1074,false)]
theorem der_15763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15763 :=
  CNF.rup_sound cl_15763 [cl_14706,cl_14707,cl_13729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13729 v h) (by intro d hd; cases hd))))
def cl_15764 : CNF.NClause := [(1069,false),(1074,true),(1059,true),(1064,true)]
theorem der_15764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15764 :=
  CNF.rup_sound cl_15764 [cl_14706,cl_14707,cl_13730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13730 v h) (by intro d hd; cases hd))))
def cl_15765 : CNF.NClause := [(1064,false),(1069,true),(1059,true),(1074,true)]
theorem der_15765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15765 :=
  CNF.rup_sound cl_15765 [cl_14706,cl_14707,cl_13731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13731 v h) (by intro d hd; cases hd))))
def cl_15766 : CNF.NClause := [(1059,false),(1064,true),(1069,true),(1074,true)]
theorem der_15766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15766 :=
  CNF.rup_sound cl_15766 [cl_14706,cl_14707,cl_13732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (inp_13732 v h) (by intro d hd; cases hd))))
def cl_15767 : CNF.NClause := [(1,true),(125,false)]
theorem der_15767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15767 :=
  CNF.rup_sound cl_15767 [cl_14696,cl_13766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13766 v h) (by intro d hd; cases hd)))
def cl_15768 : CNF.NClause := [(2,true),(126,false)]
theorem der_15768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15768 :=
  CNF.rup_sound cl_15768 [cl_14696,cl_13767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13767 v h) (by intro d hd; cases hd)))
def cl_15769 : CNF.NClause := [(3,true),(127,false)]
theorem der_15769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15769 :=
  CNF.rup_sound cl_15769 [cl_14696,cl_13768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13768 v h) (by intro d hd; cases hd)))
def cl_15770 : CNF.NClause := [(4,true),(128,false)]
theorem der_15770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15770 :=
  CNF.rup_sound cl_15770 [cl_14696,cl_13769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13769 v h) (by intro d hd; cases hd)))
def cl_15771 : CNF.NClause := [(5,true),(129,false)]
theorem der_15771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15771 :=
  CNF.rup_sound cl_15771 [cl_14696,cl_13770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13770 v h) (by intro d hd; cases hd)))
def cl_15772 : CNF.NClause := [(6,true),(130,false)]
theorem der_15772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15772 :=
  CNF.rup_sound cl_15772 [cl_14696,cl_13771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13771 v h) (by intro d hd; cases hd)))
def cl_15773 : CNF.NClause := [(7,true),(131,false)]
theorem der_15773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15773 :=
  CNF.rup_sound cl_15773 [cl_14696,cl_13772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13772 v h) (by intro d hd; cases hd)))
def cl_15774 : CNF.NClause := [(8,true),(132,false)]
theorem der_15774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15774 :=
  CNF.rup_sound cl_15774 [cl_14696,cl_13773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13773 v h) (by intro d hd; cases hd)))
def cl_15775 : CNF.NClause := [(9,true),(133,false)]
theorem der_15775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15775 :=
  CNF.rup_sound cl_15775 [cl_14696,cl_13774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13774 v h) (by intro d hd; cases hd)))
def cl_15776 : CNF.NClause := [(10,true),(134,false)]
theorem der_15776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15776 :=
  CNF.rup_sound cl_15776 [cl_14696,cl_13775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13775 v h) (by intro d hd; cases hd)))
def cl_15777 : CNF.NClause := [(11,true),(135,false)]
theorem der_15777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15777 :=
  CNF.rup_sound cl_15777 [cl_14696,cl_13776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13776 v h) (by intro d hd; cases hd)))
def cl_15778 : CNF.NClause := [(12,true),(136,false)]
theorem der_15778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15778 :=
  CNF.rup_sound cl_15778 [cl_14696,cl_13777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13777 v h) (by intro d hd; cases hd)))
def cl_15779 : CNF.NClause := [(13,true),(137,false)]
theorem der_15779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15779 :=
  CNF.rup_sound cl_15779 [cl_14696,cl_13778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13778 v h) (by intro d hd; cases hd)))
def cl_15780 : CNF.NClause := [(14,true),(138,false)]
theorem der_15780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15780 :=
  CNF.rup_sound cl_15780 [cl_14696,cl_13779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13779 v h) (by intro d hd; cases hd)))
def cl_15781 : CNF.NClause := [(15,true),(139,false)]
theorem der_15781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15781 :=
  CNF.rup_sound cl_15781 [cl_14696,cl_13780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13780 v h) (by intro d hd; cases hd)))
def cl_15782 : CNF.NClause := [(16,true),(140,false)]
theorem der_15782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15782 :=
  CNF.rup_sound cl_15782 [cl_14696,cl_13781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13781 v h) (by intro d hd; cases hd)))
def cl_15783 : CNF.NClause := [(17,true),(141,false)]
theorem der_15783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15783 :=
  CNF.rup_sound cl_15783 [cl_14696,cl_13782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13782 v h) (by intro d hd; cases hd)))
def cl_15784 : CNF.NClause := [(18,true),(142,false)]
theorem der_15784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15784 :=
  CNF.rup_sound cl_15784 [cl_14696,cl_13783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13783 v h) (by intro d hd; cases hd)))
def cl_15785 : CNF.NClause := [(19,true),(143,false)]
theorem der_15785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15785 :=
  CNF.rup_sound cl_15785 [cl_14696,cl_13784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13784 v h) (by intro d hd; cases hd)))
def cl_15786 : CNF.NClause := [(20,true),(144,false)]
theorem der_15786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15786 :=
  CNF.rup_sound cl_15786 [cl_14696,cl_13785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13785 v h) (by intro d hd; cases hd)))
def cl_15787 : CNF.NClause := [(21,true),(145,false)]
theorem der_15787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15787 :=
  CNF.rup_sound cl_15787 [cl_14696,cl_13786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13786 v h) (by intro d hd; cases hd)))
def cl_15788 : CNF.NClause := [(22,true),(146,false)]
theorem der_15788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15788 :=
  CNF.rup_sound cl_15788 [cl_14696,cl_13787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13787 v h) (by intro d hd; cases hd)))
def cl_15789 : CNF.NClause := [(23,true),(147,false)]
theorem der_15789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15789 :=
  CNF.rup_sound cl_15789 [cl_14696,cl_13788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13788 v h) (by intro d hd; cases hd)))
def cl_15790 : CNF.NClause := [(24,true),(148,false)]
theorem der_15790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15790 :=
  CNF.rup_sound cl_15790 [cl_14696,cl_13789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13789 v h) (by intro d hd; cases hd)))
def cl_15791 : CNF.NClause := [(26,true),(150,false)]
theorem der_15791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15791 :=
  CNF.rup_sound cl_15791 [cl_14696,cl_13791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13791 v h) (by intro d hd; cases hd)))
def cl_15792 : CNF.NClause := [(27,true),(151,false)]
theorem der_15792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15792 :=
  CNF.rup_sound cl_15792 [cl_14696,cl_13792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13792 v h) (by intro d hd; cases hd)))
def cl_15793 : CNF.NClause := [(28,true),(152,false)]
theorem der_15793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15793 :=
  CNF.rup_sound cl_15793 [cl_14696,cl_13793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13793 v h) (by intro d hd; cases hd)))
def cl_15794 : CNF.NClause := [(29,true),(153,false)]
theorem der_15794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15794 :=
  CNF.rup_sound cl_15794 [cl_14696,cl_13794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13794 v h) (by intro d hd; cases hd)))
def cl_15795 : CNF.NClause := [(1,true),(155,false)]
theorem der_15795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15795 :=
  CNF.rup_sound cl_15795 [cl_14696,cl_13796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13796 v h) (by intro d hd; cases hd)))
def cl_15796 : CNF.NClause := [(1,true),(180,false)]
theorem der_15796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15796 :=
  CNF.rup_sound cl_15796 [cl_14697,cl_13820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_13820 v h) (by intro d hd; cases hd)))
def cl_15797 : CNF.NClause := [(1,true),(185,false)]
theorem der_15797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15797 :=
  CNF.rup_sound cl_15797 [cl_14698,cl_13825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_13825 v h) (by intro d hd; cases hd)))
def cl_15798 : CNF.NClause := [(2,true),(186,false)]
theorem der_15798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15798 :=
  CNF.rup_sound cl_15798 [cl_14696,cl_13826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13826 v h) (by intro d hd; cases hd)))
def cl_15799 : CNF.NClause := [(2,true),(211,false)]
theorem der_15799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15799 :=
  CNF.rup_sound cl_15799 [cl_14697,cl_13850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_13850 v h) (by intro d hd; cases hd)))
def cl_15800 : CNF.NClause := [(2,true),(216,false)]
theorem der_15800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15800 :=
  CNF.rup_sound cl_15800 [cl_14698,cl_13855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_13855 v h) (by intro d hd; cases hd)))
def cl_15801 : CNF.NClause := [(3,true),(217,false)]
theorem der_15801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15801 :=
  CNF.rup_sound cl_15801 [cl_14696,cl_13856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13856 v h) (by intro d hd; cases hd)))
def cl_15802 : CNF.NClause := [(3,true),(242,false)]
theorem der_15802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15802 :=
  CNF.rup_sound cl_15802 [cl_14697,cl_13880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_13880 v h) (by intro d hd; cases hd)))
def cl_15803 : CNF.NClause := [(3,true),(247,false)]
theorem der_15803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15803 :=
  CNF.rup_sound cl_15803 [cl_14698,cl_13885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_13885 v h) (by intro d hd; cases hd)))
def cl_15804 : CNF.NClause := [(4,true),(248,false)]
theorem der_15804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15804 :=
  CNF.rup_sound cl_15804 [cl_14696,cl_13886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13886 v h) (by intro d hd; cases hd)))
def cl_15805 : CNF.NClause := [(4,true),(273,false)]
theorem der_15805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15805 :=
  CNF.rup_sound cl_15805 [cl_14697,cl_13910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_13910 v h) (by intro d hd; cases hd)))
def cl_15806 : CNF.NClause := [(4,true),(278,false)]
theorem der_15806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15806 :=
  CNF.rup_sound cl_15806 [cl_14698,cl_13915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_13915 v h) (by intro d hd; cases hd)))
def cl_15807 : CNF.NClause := [(5,true),(279,false)]
theorem der_15807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15807 :=
  CNF.rup_sound cl_15807 [cl_14696,cl_13916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13916 v h) (by intro d hd; cases hd)))
def cl_15808 : CNF.NClause := [(5,true),(304,false)]
theorem der_15808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15808 :=
  CNF.rup_sound cl_15808 [cl_14697,cl_13940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_13940 v h) (by intro d hd; cases hd)))
def cl_15809 : CNF.NClause := [(5,true),(309,false)]
theorem der_15809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15809 :=
  CNF.rup_sound cl_15809 [cl_14698,cl_13945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_13945 v h) (by intro d hd; cases hd)))
def cl_15810 : CNF.NClause := [(6,true),(310,false)]
theorem der_15810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15810 :=
  CNF.rup_sound cl_15810 [cl_14696,cl_13946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13946 v h) (by intro d hd; cases hd)))
def cl_15811 : CNF.NClause := [(6,true),(335,false)]
theorem der_15811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15811 :=
  CNF.rup_sound cl_15811 [cl_14697,cl_13970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_13970 v h) (by intro d hd; cases hd)))
def cl_15812 : CNF.NClause := [(6,true),(340,false)]
theorem der_15812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15812 :=
  CNF.rup_sound cl_15812 [cl_14698,cl_13975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_13975 v h) (by intro d hd; cases hd)))
def cl_15813 : CNF.NClause := [(7,true),(341,false)]
theorem der_15813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15813 :=
  CNF.rup_sound cl_15813 [cl_14696,cl_13976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13976 v h) (by intro d hd; cases hd)))
def cl_15814 : CNF.NClause := [(7,true),(366,false)]
theorem der_15814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15814 :=
  CNF.rup_sound cl_15814 [cl_14697,cl_14000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14000 v h) (by intro d hd; cases hd)))
def cl_15815 : CNF.NClause := [(7,true),(371,false)]
theorem der_15815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15815 :=
  CNF.rup_sound cl_15815 [cl_14698,cl_14005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14005 v h) (by intro d hd; cases hd)))
def cl_15816 : CNF.NClause := [(8,true),(372,false)]
theorem der_15816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15816 :=
  CNF.rup_sound cl_15816 [cl_14696,cl_14006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14006 v h) (by intro d hd; cases hd)))
def cl_15817 : CNF.NClause := [(8,true),(397,false)]
theorem der_15817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15817 :=
  CNF.rup_sound cl_15817 [cl_14697,cl_14030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14030 v h) (by intro d hd; cases hd)))
def cl_15818 : CNF.NClause := [(8,true),(402,false)]
theorem der_15818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15818 :=
  CNF.rup_sound cl_15818 [cl_14698,cl_14035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14035 v h) (by intro d hd; cases hd)))
def cl_15819 : CNF.NClause := [(9,true),(403,false)]
theorem der_15819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15819 :=
  CNF.rup_sound cl_15819 [cl_14696,cl_14036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14036 v h) (by intro d hd; cases hd)))
def cl_15820 : CNF.NClause := [(9,true),(428,false)]
theorem der_15820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15820 :=
  CNF.rup_sound cl_15820 [cl_14697,cl_14060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14060 v h) (by intro d hd; cases hd)))
def cl_15821 : CNF.NClause := [(9,true),(433,false)]
theorem der_15821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15821 :=
  CNF.rup_sound cl_15821 [cl_14698,cl_14065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14065 v h) (by intro d hd; cases hd)))
def cl_15822 : CNF.NClause := [(10,true),(434,false)]
theorem der_15822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15822 :=
  CNF.rup_sound cl_15822 [cl_14696,cl_14066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14066 v h) (by intro d hd; cases hd)))
def cl_15823 : CNF.NClause := [(10,true),(459,false)]
theorem der_15823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15823 :=
  CNF.rup_sound cl_15823 [cl_14697,cl_14090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14090 v h) (by intro d hd; cases hd)))
def cl_15824 : CNF.NClause := [(10,true),(464,false)]
theorem der_15824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15824 :=
  CNF.rup_sound cl_15824 [cl_14698,cl_14095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14095 v h) (by intro d hd; cases hd)))
def cl_15825 : CNF.NClause := [(11,true),(465,false)]
theorem der_15825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15825 :=
  CNF.rup_sound cl_15825 [cl_14696,cl_14096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14096 v h) (by intro d hd; cases hd)))
def cl_15826 : CNF.NClause := [(11,true),(490,false)]
theorem der_15826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15826 :=
  CNF.rup_sound cl_15826 [cl_14697,cl_14120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14120 v h) (by intro d hd; cases hd)))
def cl_15827 : CNF.NClause := [(11,true),(495,false)]
theorem der_15827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15827 :=
  CNF.rup_sound cl_15827 [cl_14698,cl_14125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14125 v h) (by intro d hd; cases hd)))
def cl_15828 : CNF.NClause := [(12,true),(496,false)]
theorem der_15828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15828 :=
  CNF.rup_sound cl_15828 [cl_14696,cl_14126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14126 v h) (by intro d hd; cases hd)))
def cl_15829 : CNF.NClause := [(12,true),(521,false)]
theorem der_15829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15829 :=
  CNF.rup_sound cl_15829 [cl_14697,cl_14150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14150 v h) (by intro d hd; cases hd)))
def cl_15830 : CNF.NClause := [(12,true),(526,false)]
theorem der_15830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15830 :=
  CNF.rup_sound cl_15830 [cl_14698,cl_14155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14155 v h) (by intro d hd; cases hd)))
def cl_15831 : CNF.NClause := [(13,true),(527,false)]
theorem der_15831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15831 :=
  CNF.rup_sound cl_15831 [cl_14696,cl_14156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14156 v h) (by intro d hd; cases hd)))
def cl_15832 : CNF.NClause := [(13,true),(552,false)]
theorem der_15832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15832 :=
  CNF.rup_sound cl_15832 [cl_14697,cl_14180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14180 v h) (by intro d hd; cases hd)))
def cl_15833 : CNF.NClause := [(13,true),(557,false)]
theorem der_15833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15833 :=
  CNF.rup_sound cl_15833 [cl_14698,cl_14185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14185 v h) (by intro d hd; cases hd)))
def cl_15834 : CNF.NClause := [(14,true),(558,false)]
theorem der_15834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15834 :=
  CNF.rup_sound cl_15834 [cl_14696,cl_14186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14186 v h) (by intro d hd; cases hd)))
def cl_15835 : CNF.NClause := [(14,true),(583,false)]
theorem der_15835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15835 :=
  CNF.rup_sound cl_15835 [cl_14697,cl_14210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14210 v h) (by intro d hd; cases hd)))
def cl_15836 : CNF.NClause := [(14,true),(588,false)]
theorem der_15836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15836 :=
  CNF.rup_sound cl_15836 [cl_14698,cl_14215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14215 v h) (by intro d hd; cases hd)))
def cl_15837 : CNF.NClause := [(15,true),(589,false)]
theorem der_15837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15837 :=
  CNF.rup_sound cl_15837 [cl_14696,cl_14216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14216 v h) (by intro d hd; cases hd)))
def cl_15838 : CNF.NClause := [(15,true),(614,false)]
theorem der_15838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15838 :=
  CNF.rup_sound cl_15838 [cl_14697,cl_14240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14240 v h) (by intro d hd; cases hd)))
def cl_15839 : CNF.NClause := [(15,true),(619,false)]
theorem der_15839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15839 :=
  CNF.rup_sound cl_15839 [cl_14698,cl_14245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14245 v h) (by intro d hd; cases hd)))
def cl_15840 : CNF.NClause := [(16,true),(620,false)]
theorem der_15840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15840 :=
  CNF.rup_sound cl_15840 [cl_14696,cl_14246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14246 v h) (by intro d hd; cases hd)))
def cl_15841 : CNF.NClause := [(16,true),(645,false)]
theorem der_15841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15841 :=
  CNF.rup_sound cl_15841 [cl_14697,cl_14270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14270 v h) (by intro d hd; cases hd)))
def cl_15842 : CNF.NClause := [(16,true),(650,false)]
theorem der_15842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15842 :=
  CNF.rup_sound cl_15842 [cl_14698,cl_14275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14275 v h) (by intro d hd; cases hd)))
def cl_15843 : CNF.NClause := [(17,true),(651,false)]
theorem der_15843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15843 :=
  CNF.rup_sound cl_15843 [cl_14696,cl_14276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14276 v h) (by intro d hd; cases hd)))
def cl_15844 : CNF.NClause := [(17,true),(676,false)]
theorem der_15844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15844 :=
  CNF.rup_sound cl_15844 [cl_14697,cl_14300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14300 v h) (by intro d hd; cases hd)))
def cl_15845 : CNF.NClause := [(17,true),(681,false)]
theorem der_15845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15845 :=
  CNF.rup_sound cl_15845 [cl_14698,cl_14305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14305 v h) (by intro d hd; cases hd)))
def cl_15846 : CNF.NClause := [(18,true),(682,false)]
theorem der_15846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15846 :=
  CNF.rup_sound cl_15846 [cl_14696,cl_14306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14306 v h) (by intro d hd; cases hd)))
def cl_15847 : CNF.NClause := [(18,true),(707,false)]
theorem der_15847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15847 :=
  CNF.rup_sound cl_15847 [cl_14697,cl_14330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14330 v h) (by intro d hd; cases hd)))
def cl_15848 : CNF.NClause := [(18,true),(712,false)]
theorem der_15848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15848 :=
  CNF.rup_sound cl_15848 [cl_14698,cl_14335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14335 v h) (by intro d hd; cases hd)))
def cl_15849 : CNF.NClause := [(19,true),(713,false)]
theorem der_15849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15849 :=
  CNF.rup_sound cl_15849 [cl_14696,cl_14336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14336 v h) (by intro d hd; cases hd)))
def cl_15850 : CNF.NClause := [(19,true),(738,false)]
theorem der_15850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15850 :=
  CNF.rup_sound cl_15850 [cl_14697,cl_14360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14360 v h) (by intro d hd; cases hd)))
def cl_15851 : CNF.NClause := [(19,true),(743,false)]
theorem der_15851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15851 :=
  CNF.rup_sound cl_15851 [cl_14698,cl_14365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14365 v h) (by intro d hd; cases hd)))
def cl_15852 : CNF.NClause := [(20,true),(744,false)]
theorem der_15852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15852 :=
  CNF.rup_sound cl_15852 [cl_14696,cl_14366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14366 v h) (by intro d hd; cases hd)))
def cl_15853 : CNF.NClause := [(20,true),(769,false)]
theorem der_15853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15853 :=
  CNF.rup_sound cl_15853 [cl_14697,cl_14390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14390 v h) (by intro d hd; cases hd)))
def cl_15854 : CNF.NClause := [(20,true),(774,false)]
theorem der_15854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15854 :=
  CNF.rup_sound cl_15854 [cl_14698,cl_14395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14395 v h) (by intro d hd; cases hd)))
def cl_15855 : CNF.NClause := [(21,true),(775,false)]
theorem der_15855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15855 :=
  CNF.rup_sound cl_15855 [cl_14696,cl_14396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14396 v h) (by intro d hd; cases hd)))
def cl_15856 : CNF.NClause := [(21,true),(800,false)]
theorem der_15856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15856 :=
  CNF.rup_sound cl_15856 [cl_14697,cl_14420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14420 v h) (by intro d hd; cases hd)))
def cl_15857 : CNF.NClause := [(21,true),(805,false)]
theorem der_15857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15857 :=
  CNF.rup_sound cl_15857 [cl_14698,cl_14425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14425 v h) (by intro d hd; cases hd)))
def cl_15858 : CNF.NClause := [(22,true),(806,false)]
theorem der_15858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15858 :=
  CNF.rup_sound cl_15858 [cl_14696,cl_14426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14426 v h) (by intro d hd; cases hd)))
def cl_15859 : CNF.NClause := [(22,true),(831,false)]
theorem der_15859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15859 :=
  CNF.rup_sound cl_15859 [cl_14697,cl_14450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14450 v h) (by intro d hd; cases hd)))
def cl_15860 : CNF.NClause := [(22,true),(836,false)]
theorem der_15860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15860 :=
  CNF.rup_sound cl_15860 [cl_14698,cl_14455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14455 v h) (by intro d hd; cases hd)))
def cl_15861 : CNF.NClause := [(23,true),(837,false)]
theorem der_15861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15861 :=
  CNF.rup_sound cl_15861 [cl_14696,cl_14456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14456 v h) (by intro d hd; cases hd)))
def cl_15862 : CNF.NClause := [(23,true),(862,false)]
theorem der_15862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15862 :=
  CNF.rup_sound cl_15862 [cl_14697,cl_14480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14480 v h) (by intro d hd; cases hd)))
def cl_15863 : CNF.NClause := [(23,true),(867,false)]
theorem der_15863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15863 :=
  CNF.rup_sound cl_15863 [cl_14698,cl_14485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14485 v h) (by intro d hd; cases hd)))
def cl_15864 : CNF.NClause := [(24,true),(868,false)]
theorem der_15864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15864 :=
  CNF.rup_sound cl_15864 [cl_14696,cl_14486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14486 v h) (by intro d hd; cases hd)))
def cl_15865 : CNF.NClause := [(24,true),(893,false)]
theorem der_15865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15865 :=
  CNF.rup_sound cl_15865 [cl_14697,cl_14510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14510 v h) (by intro d hd; cases hd)))
def cl_15866 : CNF.NClause := [(24,true),(898,false)]
theorem der_15866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15866 :=
  CNF.rup_sound cl_15866 [cl_14698,cl_14515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14515 v h) (by intro d hd; cases hd)))
def cl_15867 : CNF.NClause := [(1,true),(900,false)]
theorem der_15867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15867 :=
  CNF.rup_sound cl_15867 [cl_14697,cl_14517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14517 v h) (by intro d hd; cases hd)))
def cl_15868 : CNF.NClause := [(2,true),(901,false)]
theorem der_15868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15868 :=
  CNF.rup_sound cl_15868 [cl_14697,cl_14518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14518 v h) (by intro d hd; cases hd)))
def cl_15869 : CNF.NClause := [(3,true),(902,false)]
theorem der_15869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15869 :=
  CNF.rup_sound cl_15869 [cl_14697,cl_14519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14519 v h) (by intro d hd; cases hd)))
def cl_15870 : CNF.NClause := [(4,true),(903,false)]
theorem der_15870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15870 :=
  CNF.rup_sound cl_15870 [cl_14697,cl_14520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14520 v h) (by intro d hd; cases hd)))
def cl_15871 : CNF.NClause := [(5,true),(904,false)]
theorem der_15871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15871 :=
  CNF.rup_sound cl_15871 [cl_14697,cl_14521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14521 v h) (by intro d hd; cases hd)))
def cl_15872 : CNF.NClause := [(6,true),(905,false)]
theorem der_15872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15872 :=
  CNF.rup_sound cl_15872 [cl_14697,cl_14522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14522 v h) (by intro d hd; cases hd)))
def cl_15873 : CNF.NClause := [(7,true),(906,false)]
theorem der_15873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15873 :=
  CNF.rup_sound cl_15873 [cl_14697,cl_14523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14523 v h) (by intro d hd; cases hd)))
def cl_15874 : CNF.NClause := [(8,true),(907,false)]
theorem der_15874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15874 :=
  CNF.rup_sound cl_15874 [cl_14697,cl_14524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14524 v h) (by intro d hd; cases hd)))
def cl_15875 : CNF.NClause := [(9,true),(908,false)]
theorem der_15875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15875 :=
  CNF.rup_sound cl_15875 [cl_14697,cl_14525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14525 v h) (by intro d hd; cases hd)))
def cl_15876 : CNF.NClause := [(10,true),(909,false)]
theorem der_15876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15876 :=
  CNF.rup_sound cl_15876 [cl_14697,cl_14526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14526 v h) (by intro d hd; cases hd)))
def cl_15877 : CNF.NClause := [(11,true),(910,false)]
theorem der_15877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15877 :=
  CNF.rup_sound cl_15877 [cl_14697,cl_14527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14527 v h) (by intro d hd; cases hd)))
def cl_15878 : CNF.NClause := [(12,true),(911,false)]
theorem der_15878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15878 :=
  CNF.rup_sound cl_15878 [cl_14697,cl_14528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14528 v h) (by intro d hd; cases hd)))
def cl_15879 : CNF.NClause := [(13,true),(912,false)]
theorem der_15879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15879 :=
  CNF.rup_sound cl_15879 [cl_14697,cl_14529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14529 v h) (by intro d hd; cases hd)))
def cl_15880 : CNF.NClause := [(14,true),(913,false)]
theorem der_15880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15880 :=
  CNF.rup_sound cl_15880 [cl_14697,cl_14530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14530 v h) (by intro d hd; cases hd)))
def cl_15881 : CNF.NClause := [(15,true),(914,false)]
theorem der_15881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15881 :=
  CNF.rup_sound cl_15881 [cl_14697,cl_14531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14531 v h) (by intro d hd; cases hd)))
def cl_15882 : CNF.NClause := [(16,true),(915,false)]
theorem der_15882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15882 :=
  CNF.rup_sound cl_15882 [cl_14697,cl_14532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14532 v h) (by intro d hd; cases hd)))
def cl_15883 : CNF.NClause := [(17,true),(916,false)]
theorem der_15883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15883 :=
  CNF.rup_sound cl_15883 [cl_14697,cl_14533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14533 v h) (by intro d hd; cases hd)))
def cl_15884 : CNF.NClause := [(18,true),(917,false)]
theorem der_15884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15884 :=
  CNF.rup_sound cl_15884 [cl_14697,cl_14534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14534 v h) (by intro d hd; cases hd)))
def cl_15885 : CNF.NClause := [(19,true),(918,false)]
theorem der_15885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15885 :=
  CNF.rup_sound cl_15885 [cl_14697,cl_14535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14535 v h) (by intro d hd; cases hd)))
def cl_15886 : CNF.NClause := [(20,true),(919,false)]
theorem der_15886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15886 :=
  CNF.rup_sound cl_15886 [cl_14697,cl_14536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14536 v h) (by intro d hd; cases hd)))
def cl_15887 : CNF.NClause := [(21,true),(920,false)]
theorem der_15887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15887 :=
  CNF.rup_sound cl_15887 [cl_14697,cl_14537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14537 v h) (by intro d hd; cases hd)))
def cl_15888 : CNF.NClause := [(22,true),(921,false)]
theorem der_15888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15888 :=
  CNF.rup_sound cl_15888 [cl_14697,cl_14538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14538 v h) (by intro d hd; cases hd)))
def cl_15889 : CNF.NClause := [(23,true),(922,false)]
theorem der_15889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15889 :=
  CNF.rup_sound cl_15889 [cl_14697,cl_14539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14539 v h) (by intro d hd; cases hd)))
def cl_15890 : CNF.NClause := [(24,true),(923,false)]
theorem der_15890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15890 :=
  CNF.rup_sound cl_15890 [cl_14697,cl_14540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14540 v h) (by intro d hd; cases hd)))
def cl_15891 : CNF.NClause := [(26,true),(925,false)]
theorem der_15891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15891 :=
  CNF.rup_sound cl_15891 [cl_14697,cl_14541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14541 v h) (by intro d hd; cases hd)))
def cl_15892 : CNF.NClause := [(27,true),(926,false)]
theorem der_15892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15892 :=
  CNF.rup_sound cl_15892 [cl_14697,cl_14542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14542 v h) (by intro d hd; cases hd)))
def cl_15893 : CNF.NClause := [(28,true),(927,false)]
theorem der_15893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15893 :=
  CNF.rup_sound cl_15893 [cl_14697,cl_14543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14543 v h) (by intro d hd; cases hd)))
def cl_15894 : CNF.NClause := [(29,true),(928,false)]
theorem der_15894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15894 :=
  CNF.rup_sound cl_15894 [cl_14697,cl_14544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14544 v h) (by intro d hd; cases hd)))
def cl_15895 : CNF.NClause := [(26,true),(930,false)]
theorem der_15895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15895 :=
  CNF.rup_sound cl_15895 [cl_14696,cl_14546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14546 v h) (by intro d hd; cases hd)))
def cl_15896 : CNF.NClause := [(26,true),(955,false)]
theorem der_15896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15896 :=
  CNF.rup_sound cl_15896 [cl_14697,cl_14571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14571 v h) (by intro d hd; cases hd)))
def cl_15897 : CNF.NClause := [(26,true),(960,false)]
theorem der_15897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15897 :=
  CNF.rup_sound cl_15897 [cl_14698,cl_14575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14575 v h) (by intro d hd; cases hd)))
def cl_15898 : CNF.NClause := [(27,true),(961,false)]
theorem der_15898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15898 :=
  CNF.rup_sound cl_15898 [cl_14696,cl_14576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14576 v h) (by intro d hd; cases hd)))
def cl_15899 : CNF.NClause := [(27,true),(986,false)]
theorem der_15899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15899 :=
  CNF.rup_sound cl_15899 [cl_14697,cl_14601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14601 v h) (by intro d hd; cases hd)))
def cl_15900 : CNF.NClause := [(27,true),(991,false)]
theorem der_15900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15900 :=
  CNF.rup_sound cl_15900 [cl_14698,cl_14605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14605 v h) (by intro d hd; cases hd)))
def cl_15901 : CNF.NClause := [(28,true),(992,false)]
theorem der_15901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15901 :=
  CNF.rup_sound cl_15901 [cl_14696,cl_14606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14606 v h) (by intro d hd; cases hd)))
def cl_15902 : CNF.NClause := [(28,true),(1017,false)]
theorem der_15902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15902 :=
  CNF.rup_sound cl_15902 [cl_14697,cl_14631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14631 v h) (by intro d hd; cases hd)))
def cl_15903 : CNF.NClause := [(28,true),(1022,false)]
theorem der_15903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15903 :=
  CNF.rup_sound cl_15903 [cl_14698,cl_14635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14635 v h) (by intro d hd; cases hd)))
def cl_15904 : CNF.NClause := [(29,true),(1023,false)]
theorem der_15904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15904 :=
  CNF.rup_sound cl_15904 [cl_14696,cl_14636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14636 v h) (by intro d hd; cases hd)))
def cl_15905 : CNF.NClause := [(29,true),(1048,false)]
theorem der_15905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15905 :=
  CNF.rup_sound cl_15905 [cl_14697,cl_14661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14661 v h) (by intro d hd; cases hd)))
def cl_15906 : CNF.NClause := [(29,true),(1053,false)]
theorem der_15906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15906 :=
  CNF.rup_sound cl_15906 [cl_14698,cl_14665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14665 v h) (by intro d hd; cases hd)))
def cl_15907 : CNF.NClause := [(1,true),(1055,false)]
theorem der_15907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15907 :=
  CNF.rup_sound cl_15907 [cl_14698,cl_14667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14667 v h) (by intro d hd; cases hd)))
def cl_15908 : CNF.NClause := [(2,true),(1056,false)]
theorem der_15908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15908 :=
  CNF.rup_sound cl_15908 [cl_14698,cl_14668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14668 v h) (by intro d hd; cases hd)))
def cl_15909 : CNF.NClause := [(3,true),(1057,false)]
theorem der_15909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15909 :=
  CNF.rup_sound cl_15909 [cl_14698,cl_14669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14669 v h) (by intro d hd; cases hd)))
def cl_15910 : CNF.NClause := [(4,true),(1058,false)]
theorem der_15910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15910 :=
  CNF.rup_sound cl_15910 [cl_14698,cl_14670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14670 v h) (by intro d hd; cases hd)))
def cl_15911 : CNF.NClause := [(5,true),(1059,false)]
theorem der_15911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15911 :=
  CNF.rup_sound cl_15911 [cl_14698,cl_14671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14671 v h) (by intro d hd; cases hd)))
def cl_15912 : CNF.NClause := [(6,true),(1060,false)]
theorem der_15912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15912 :=
  CNF.rup_sound cl_15912 [cl_14698,cl_14672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14672 v h) (by intro d hd; cases hd)))
def cl_15913 : CNF.NClause := [(7,true),(1061,false)]
theorem der_15913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15913 :=
  CNF.rup_sound cl_15913 [cl_14698,cl_14673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14673 v h) (by intro d hd; cases hd)))
def cl_15914 : CNF.NClause := [(8,true),(1062,false)]
theorem der_15914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15914 :=
  CNF.rup_sound cl_15914 [cl_14698,cl_14674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14674 v h) (by intro d hd; cases hd)))
def cl_15915 : CNF.NClause := [(9,true),(1063,false)]
theorem der_15915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15915 :=
  CNF.rup_sound cl_15915 [cl_14698,cl_14675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14675 v h) (by intro d hd; cases hd)))
def cl_15916 : CNF.NClause := [(10,true),(1064,false)]
theorem der_15916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15916 :=
  CNF.rup_sound cl_15916 [cl_14698,cl_14676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14676 v h) (by intro d hd; cases hd)))
def cl_15917 : CNF.NClause := [(11,true),(1065,false)]
theorem der_15917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15917 :=
  CNF.rup_sound cl_15917 [cl_14698,cl_14677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14677 v h) (by intro d hd; cases hd)))
def cl_15918 : CNF.NClause := [(12,true),(1066,false)]
theorem der_15918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15918 :=
  CNF.rup_sound cl_15918 [cl_14698,cl_14678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14678 v h) (by intro d hd; cases hd)))
def cl_15919 : CNF.NClause := [(13,true),(1067,false)]
theorem der_15919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15919 :=
  CNF.rup_sound cl_15919 [cl_14698,cl_14679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14679 v h) (by intro d hd; cases hd)))
def cl_15920 : CNF.NClause := [(14,true),(1068,false)]
theorem der_15920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15920 :=
  CNF.rup_sound cl_15920 [cl_14698,cl_14680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14680 v h) (by intro d hd; cases hd)))
def cl_15921 : CNF.NClause := [(15,true),(1069,false)]
theorem der_15921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15921 :=
  CNF.rup_sound cl_15921 [cl_14698,cl_14681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14681 v h) (by intro d hd; cases hd)))
def cl_15922 : CNF.NClause := [(16,true),(1070,false)]
theorem der_15922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15922 :=
  CNF.rup_sound cl_15922 [cl_14698,cl_14682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14682 v h) (by intro d hd; cases hd)))
def cl_15923 : CNF.NClause := [(17,true),(1071,false)]
theorem der_15923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15923 :=
  CNF.rup_sound cl_15923 [cl_14698,cl_14683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14683 v h) (by intro d hd; cases hd)))
def cl_15924 : CNF.NClause := [(18,true),(1072,false)]
theorem der_15924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15924 :=
  CNF.rup_sound cl_15924 [cl_14698,cl_14684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14684 v h) (by intro d hd; cases hd)))
def cl_15925 : CNF.NClause := [(19,true),(1073,false)]
theorem der_15925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15925 :=
  CNF.rup_sound cl_15925 [cl_14698,cl_14685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14685 v h) (by intro d hd; cases hd)))
def cl_15926 : CNF.NClause := [(20,true),(1074,false)]
theorem der_15926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15926 :=
  CNF.rup_sound cl_15926 [cl_14698,cl_14686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14686 v h) (by intro d hd; cases hd)))
def cl_15927 : CNF.NClause := [(21,true),(1075,false)]
theorem der_15927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15927 :=
  CNF.rup_sound cl_15927 [cl_14698,cl_14687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14687 v h) (by intro d hd; cases hd)))
def cl_15928 : CNF.NClause := [(22,true),(1076,false)]
theorem der_15928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15928 :=
  CNF.rup_sound cl_15928 [cl_14698,cl_14688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14688 v h) (by intro d hd; cases hd)))
def cl_15929 : CNF.NClause := [(23,true),(1077,false)]
theorem der_15929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15929 :=
  CNF.rup_sound cl_15929 [cl_14698,cl_14689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14689 v h) (by intro d hd; cases hd)))
def cl_15930 : CNF.NClause := [(24,true),(1078,false)]
theorem der_15930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15930 :=
  CNF.rup_sound cl_15930 [cl_14698,cl_14690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14690 v h) (by intro d hd; cases hd)))
def cl_15931 : CNF.NClause := [(26,true),(1080,false)]
theorem der_15931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15931 :=
  CNF.rup_sound cl_15931 [cl_14698,cl_14692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14692 v h) (by intro d hd; cases hd)))
def cl_15932 : CNF.NClause := [(27,true),(1081,false)]
theorem der_15932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15932 :=
  CNF.rup_sound cl_15932 [cl_14698,cl_14693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14693 v h) (by intro d hd; cases hd)))
def cl_15933 : CNF.NClause := [(28,true),(1082,false)]
theorem der_15933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15933 :=
  CNF.rup_sound cl_15933 [cl_14698,cl_14694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14694 v h) (by intro d hd; cases hd)))
def cl_15934 : CNF.NClause := [(29,true),(1083,false)]
theorem der_15934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15934 :=
  CNF.rup_sound cl_15934 [cl_14698,cl_14695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14695 v h) (by intro d hd; cases hd)))
def cl_16140 : CNF.NClause := [(95,true),(56,true),(43,false),(33,false),(48,true),(53,false)]
theorem der_16140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16140 :=
  CNF.rup_sound cl_16140 [cl_2153,cl_2155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2153 v h) (hints_cons _ _ _ (inp_2155 v h) (by intro d hd; cases hd)))
def cl_16142 : CNF.NClause := [(64,true),(17,true),(2,false),(22,false),(12,false)]
theorem der_16142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16142 :=
  CNF.rup_sound cl_16142 [cl_15055,cl_15057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15055 v h) (hints_cons _ _ _ (der_15057 v h) (by intro d hd; cases hd)))
def cl_16144 : CNF.NClause := [(71,true),(13,true),(1,false),(26,false),(19,true),(20,false)]
theorem der_16144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16144 :=
  CNF.rup_sound cl_16144 [cl_589,cl_591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_589 v h) (hints_cons _ _ _ (inp_591 v h) (by intro d hd; cases hd)))
def cl_16146 : CNF.NClause := [(73,true),(18,true),(4,false),(28,false),(10,false),(21,true)]
theorem der_16146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16146 :=
  CNF.rup_sound cl_16146 [cl_729,cl_731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_729 v h) (hints_cons _ _ _ (inp_731 v h) (by intro d hd; cases hd)))
def cl_16162 : CNF.NClause := [(71,true),(13,false),(19,true),(26,false),(1,false),(20,false)]
theorem der_16162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16162 :=
  CNF.rup_sound cl_16162 [cl_585,cl_587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_585 v h) (hints_cons _ _ _ (inp_587 v h) (by intro d hd; cases hd)))
def cl_16166 : CNF.NClause := [(89,true),(14,true),(27,false),(16,true),(23,false)]
theorem der_16166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16166 :=
  CNF.rup_sound cl_16166 [cl_15319,cl_15320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15319 v h) (hints_cons _ _ _ (der_15320 v h) (by intro d hd; cases hd)))
def cl_16178 : CNF.NClause := [(89,true),(14,false),(27,false),(16,true),(23,false)]
theorem der_16178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16178 :=
  CNF.rup_sound cl_16178 [cl_15317,cl_15318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15317 v h) (hints_cons _ _ _ (der_15318 v h) (by intro d hd; cases hd)))
def cl_16191 : CNF.NClause := [(71,true),(13,true),(1,false),(26,false),(19,false),(20,false)]
theorem der_16191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16191 :=
  CNF.rup_sound cl_16191 [cl_581,cl_583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_581 v h) (hints_cons _ _ _ (inp_583 v h) (by intro d hd; cases hd)))
def cl_16193 : CNF.NClause := [(73,true),(18,false),(4,false),(28,false),(10,false),(21,true)]
theorem der_16193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16193 :=
  CNF.rup_sound cl_16193 [cl_721,cl_723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_721 v h) (hints_cons _ _ _ (inp_723 v h) (by intro d hd; cases hd)))
def cl_16262 : CNF.NClause := [(82,true),(5,false),(8,false),(6,false)]
theorem der_16262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16262 :=
  CNF.rup_sound cl_16262 [cl_14729,cl_14736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14729 v h) (hints_cons _ _ _ (der_14736 v h) (by intro d hd; cases hd)))
def cl_16816 : CNF.NClause := [(1083,true),(1078,true),(1070,true),(1066,true),(1065,true),(1064,true),(1062,true),(1061,true),(1059,true),(1058,false),(1057,true)]
theorem der_16816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16816 :=
  CNF.rup_sound cl_16816 [cl_13589,cl_13658,cl_15763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13589 v h) (hints_cons _ _ _ (inp_13658 v h) (hints_cons _ _ _ (der_15763 v h) (by intro d hd; cases hd))))
def cl_16819 : CNF.NClause := [(150,true),(147,true),(140,true),(136,true),(135,true),(134,true),(133,true),(131,true),(129,true),(128,false),(127,true),(126,true)]
theorem der_16819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16819 :=
  CNF.rup_sound cl_16819 [cl_8047,cl_8099,cl_15627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8047 v h) (hints_cons _ _ _ (inp_8099 v h) (hints_cons _ _ _ (der_15627 v h) (by intro d hd; cases hd))))
def cl_17148 : CNF.NClause := [(146,true),(153,true),(151,true),(137,true),(136,true),(135,true),(134,true),(132,true),(131,true),(130,true),(127,true),(126,true),(125,true)]
theorem der_17148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17148 :=
  CNF.rup_sound cl_17148 [cl_15661,cl_15627,cl_8069,cl_8053,cl_8078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15627 v h) (hints_cons _ _ _ (inp_8069 v h) (hints_cons _ _ _ (inp_8053 v h) (hints_cons _ _ _ (inp_8078 v h) (by intro d hd; cases hd))))))
def cl_17165 : CNF.NClause := [(146,true),(151,true),(150,true),(137,true),(138,true),(135,true),(134,true),(133,true),(132,true),(130,true),(127,true),(126,true),(125,true)]
theorem der_17165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17165 :=
  CNF.rup_sound cl_17165 [cl_15661,cl_8048,cl_8069,cl_15636,cl_8072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (inp_8048 v h) (hints_cons _ _ _ (inp_8069 v h) (hints_cons _ _ _ (der_15636 v h) (hints_cons _ _ _ (inp_8072 v h) (by intro d hd; cases hd))))))
def cl_17409 : CNF.NClause := [(137,true),(152,true),(148,true),(147,true),(135,true),(134,true),(132,true),(131,true),(130,true),(129,true),(127,true),(126,true),(125,true)]
theorem der_17409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17409 :=
  CNF.rup_sound cl_17409 [cl_15661,cl_15632,cl_8102,cl_8039,cl_15636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15632 v h) (hints_cons _ _ _ (inp_8102 v h) (hints_cons _ _ _ (inp_8039 v h) (hints_cons _ _ _ (der_15636 v h) (by intro d hd; cases hd))))))
def cl_17928 : CNF.NClause := [(920,true),(925,true),(918,true),(917,true),(910,true),(909,true),(908,true),(907,true),(906,true),(905,true),(903,true),(902,true),(900,true)]
theorem der_17928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17928 :=
  CNF.rup_sound cl_17928 [cl_15671,cl_12684,cl_12698,cl_15707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15671 v h) (hints_cons _ _ _ (inp_12684 v h) (hints_cons _ _ _ (inp_12698 v h) (hints_cons _ _ _ (der_15707 v h) (by intro d hd; cases hd)))))
def cl_19260 : CNF.NClause := [(128,true),(141,true),(126,true),(134,true),(127,true),(148,true),(153,true),(136,true),(140,true),(151,true),(144,true)]
theorem der_19260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19260 :=
  CNF.rup_sound cl_19260 [cl_8008,cl_15661,cl_8057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8008 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (inp_8057 v h) (by intro d hd; cases hd))))
def cl_19316 : CNF.NClause := [(927,true),(900,true),(904,true),(906,true),(918,true),(901,true),(923,true),(928,true),(915,true),(926,true),(919,true)]
theorem der_19316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19316 :=
  CNF.rup_sound cl_19316 [cl_15667,cl_12753,cl_12672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (inp_12753 v h) (hints_cons _ _ _ (inp_12672 v h) (by intro d hd; cases hd))))
def cl_19535 : CNF.NClause := [(920,true),(921,false),(913,true),(904,true),(906,true),(918,true),(911,true),(902,true),(923,true),(915,true),(919,true)]
theorem der_19535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19535 :=
  CNF.rup_sound cl_19535 [cl_12756,cl_15674,cl_15702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12756 v h) (hints_cons _ _ _ (der_15674 v h) (hints_cons _ _ _ (der_15702 v h) (by intro d hd; cases hd))))
def cl_19541 : CNF.NClause := [(926,true),(913,false),(921,true),(904,true),(906,true),(918,true),(911,true),(902,true),(923,true),(915,true),(919,true)]
theorem der_19541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19541 :=
  CNF.rup_sound cl_19541 [cl_12757,cl_15704,cl_15673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12757 v h) (hints_cons _ _ _ (der_15704 v h) (hints_cons _ _ _ (der_15673 v h) (by intro d hd; cases hd))))
def cl_19574 : CNF.NClause := [(914,true),(927,true),(913,true),(906,true),(911,true),(909,true),(902,true),(901,true),(923,true),(928,true),(915,true),(919,true)]
theorem der_19574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19574 :=
  CNF.rup_sound cl_19574 [cl_15716,cl_12729,cl_12754,cl_15678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15716 v h) (hints_cons _ _ _ (inp_12729 v h) (hints_cons _ _ _ (inp_12754 v h) (hints_cons _ _ _ (der_15678 v h) (by intro d hd; cases hd)))))
def cl_20033 : CNF.NClause := [(913,true),(912,true),(921,true),(922,true),(905,true),(906,true),(903,false),(911,true),(909,true),(902,true),(923,true),(928,true),(915,true)]
theorem der_20033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20033 :=
  CNF.rup_sound cl_20033 [cl_15701,cl_15680,cl_12719,cl_12728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15701 v h) (hints_cons _ _ _ (der_15680 v h) (hints_cons _ _ _ (inp_12719 v h) (hints_cons _ _ _ (inp_12728 v h) (by intro d hd; cases hd)))))
def cl_20225 : CNF.NClause := [(136,true),(145,true),(141,true),(150,true),(151,true),(131,true),(143,true),(134,true),(127,true),(126,true),(148,true),(153,true),(140,true)]
theorem der_20225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20225 :=
  CNF.rup_sound cl_20225 [cl_15618,cl_8110,cl_15626,cl_8103,cl_8050,cl_15662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15618 v h) (hints_cons _ _ _ (inp_8110 v h) (hints_cons _ _ _ (der_15626 v h) (hints_cons _ _ _ (inp_8103 v h) (hints_cons _ _ _ (inp_8050 v h) (hints_cons _ _ _ (der_15662 v h) (by intro d hd; cases hd)))))))
def cl_20270 : CNF.NClause := [(910,true),(908,true),(925,false),(912,true),(926,true),(906,true),(918,true),(911,true),(909,true),(901,true),(923,true),(928,true),(915,true),(919,true)]
theorem der_20270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20270 :=
  CNF.rup_sound cl_20270 [cl_15677,cl_12662,cl_15702,cl_15711,cl_12694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15677 v h) (hints_cons _ _ _ (inp_12662 v h) (hints_cons _ _ _ (der_15702 v h) (hints_cons _ _ _ (der_15711 v h) (hints_cons _ _ _ (inp_12694 v h) (by intro d hd; cases hd))))))
def cl_20273 : CNF.NClause := [(152,true),(133,true),(137,true),(136,true),(151,true),(131,true),(143,true),(134,true),(127,true),(126,true),(148,true),(153,true),(140,true)]
theorem der_20273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20273 :=
  CNF.rup_sound cl_20273 [cl_15620,cl_8104,cl_8047,cl_8107,cl_15627,cl_20225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (inp_8104 v h) (hints_cons _ _ _ (inp_8047 v h) (hints_cons _ _ _ (inp_8107 v h) (hints_cons _ _ _ (der_15627 v h) (hints_cons _ _ _ (der_20225 v h) (by intro d hd; cases hd)))))))
def cl_20277 : CNF.NClause := [(139,true),(141,false),(133,true),(151,true),(131,true),(143,true),(127,true),(126,true),(148,true),(153,true),(140,true),(144,true)]
theorem der_20277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20277 :=
  CNF.rup_sound cl_20277 [cl_8079,cl_15653,cl_8012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8079 v h) (hints_cons _ _ _ (der_15653 v h) (hints_cons _ _ _ (inp_8012 v h) (by intro d hd; cases hd))))
def cl_20313 : CNF.NClause := [(136,true),(133,true),(137,true),(145,true),(151,true),(131,true),(143,true),(134,true),(127,true),(126,true),(148,true),(153,true),(140,true)]
theorem der_20313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20313 :=
  CNF.rup_sound cl_20313 [cl_8110,cl_20273,cl_8100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8110 v h) (hints_cons _ _ _ (der_20273 v h) (hints_cons _ _ _ (inp_8100 v h) (by intro d hd; cases hd))))
def cl_20319 : CNF.NClause := [(135,true),(133,false),(141,true),(151,true),(131,true),(143,true),(127,true),(126,true),(148,true),(153,true),(140,true),(144,true)]
theorem der_20319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20319 :=
  CNF.rup_sound cl_20319 [cl_8078,cl_8014,cl_15652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8078 v h) (hints_cons _ _ _ (inp_8014 v h) (hints_cons _ _ _ (der_15652 v h) (by intro d hd; cases hd))))
def cl_20327 : CNF.NClause := [(152,true),(133,true),(137,true),(141,true),(151,true),(131,true),(143,true),(134,true),(127,true),(126,true),(148,true),(153,true),(140,true)]
theorem der_20327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20327 :=
  CNF.rup_sound cl_20327 [cl_15620,cl_20273,cl_8047,cl_15628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_20273 v h) (hints_cons _ _ _ (inp_8047 v h) (hints_cons _ _ _ (der_15628 v h) (by intro d hd; cases hd)))))
def cl_20330 : CNF.NClause := [(1069,true),(1063,true),(1071,true),(1081,true),(1061,true),(1073,true),(1057,true),(1056,true),(1078,true),(1083,true),(1070,true),(1074,true)]
theorem der_20330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20330 :=
  CNF.rup_sound cl_20330 [cl_13659,cl_15740,cl_13592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13659 v h) (hints_cons _ _ _ (der_15740 v h) (hints_cons _ _ _ (inp_13592 v h) (by intro d hd; cases hd))))
def cl_20341 : CNF.NClause := [(147,true),(152,true),(141,true),(151,true),(131,true),(143,true),(134,true),(127,true),(126,true),(153,true),(140,true),(144,true)]
theorem der_20341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20341 :=
  CNF.rup_sound cl_20341 [cl_8044,cl_15663,cl_8019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8044 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (inp_8019 v h) (by intro d hd; cases hd))))
def cl_20419 : CNF.NClause := [(905,true),(913,true),(912,true),(921,true),(906,true),(918,true),(903,false),(911,true),(909,true),(902,true),(901,true),(923,true),(928,true),(915,true)]
theorem der_20419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20419 :=
  CNF.rup_sound cl_20419 [cl_12691,cl_20033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12691 v h) (hints_cons _ _ _ (der_20033 v h) (by intro d hd; cases hd)))
def cl_20516 : CNF.NClause := [(905,true),(925,true),(927,true),(921,true),(906,true),(918,true),(903,false),(911,true),(909,true),(901,true),(923,true),(928,true),(919,true)]
theorem der_20516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20516 :=
  CNF.rup_sound cl_20516 [cl_12691,cl_15713,cl_15675,cl_12689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12691 v h) (hints_cons _ _ _ (der_15713 v h) (hints_cons _ _ _ (der_15675 v h) (hints_cons _ _ _ (inp_12689 v h) (by intro d hd; cases hd)))))
def cl_21038 : CNF.NClause := [(920,true),(904,true),(912,true),(916,true),(925,false),(926,true),(915,true),(921,true),(911,true),(909,true),(918,true),(928,true)]
theorem der_21038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21038 :=
  CNF.rup_sound cl_21038 [cl_15700,cl_12761,cl_12696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15700 v h) (hints_cons _ _ _ (inp_12761 v h) (hints_cons _ _ _ (inp_12696 v h) (by intro d hd; cases hd))))
def cl_21087 : CNF.NClause := [(1066,true),(1067,true),(1058,true),(1068,true),(1070,true),(1082,true),(1074,true),(1076,true),(1064,true),(1073,true),(1083,true)]
theorem der_21087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21087 :=
  CNF.rup_sound cl_21087 [cl_13588,cl_15739,cl_15756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13588 v h) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_15756 v h) (by intro d hd; cases hd))))
def cl_21150 : CNF.NClause := [(922,true),(914,true),(917,true),(913,true),(907,false),(919,true),(921,true),(911,true),(923,true),(909,true),(901,true),(918,true),(928,true)]
theorem der_21150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21150 :=
  CNF.rup_sound cl_21150 [cl_15675,cl_12694,cl_12724,cl_15711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15675 v h) (hints_cons _ _ _ (inp_12694 v h) (hints_cons _ _ _ (inp_12724 v h) (hints_cons _ _ _ (der_15711 v h) (by intro d hd; cases hd)))))
def cl_21276 : CNF.NClause := [(125,true),(151,true),(150,true),(131,true),(141,true),(136,true),(138,true),(152,true),(144,true),(146,true),(148,true),(134,true),(143,true)]
theorem der_21276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21276 :=
  CNF.rup_sound cl_21276 [cl_8056,cl_8025,cl_15664,cl_15649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8056 v h) (hints_cons _ _ _ (inp_8025 v h) (hints_cons _ _ _ (der_15664 v h) (hints_cons _ _ _ (der_15649 v h) (by intro d hd; cases hd)))))
def cl_21374 : CNF.NClause := [(922,true),(914,true),(916,true),(902,true),(917,true),(927,true),(907,false),(919,true),(921,true),(911,true),(923,true),(909,true),(901,true),(918,true),(928,true)]
theorem der_21374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21374 :=
  CNF.rup_sound cl_21374 [cl_12694,cl_21150,cl_12669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12694 v h) (hints_cons _ _ _ (der_21150 v h) (hints_cons _ _ _ (inp_12669 v h) (by intro d hd; cases hd))))
def cl_21487 : CNF.NClause := [(908,true),(900,true),(912,false),(914,true),(916,true),(927,true),(919,true),(921,true),(911,true),(923,true),(928,true)]
theorem der_21487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21487 :=
  CNF.rup_sound cl_21487 [cl_15699,cl_12733,cl_15675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15699 v h) (hints_cons _ _ _ (inp_12733 v h) (hints_cons _ _ _ (der_15675 v h) (by intro d hd; cases hd))))
def cl_21627 : CNF.NClause := [(1066,true),(1060,true),(1068,true),(1072,true),(1065,true),(1061,true),(1064,true),(1074,true),(1055,true),(1073,true),(1078,true)]
theorem der_21627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21627 :=
  CNF.rup_sound cl_21627 [cl_15739,cl_15758,cl_13605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_15758 v h) (hints_cons _ _ _ (inp_13605 v h) (by intro d hd; cases hd))))
def cl_21696 : CNF.NClause := [(1058,true),(1075,true),(1063,true),(1065,true),(1081,true),(1057,true),(1061,true),(1064,true),(1074,true),(1055,true),(1082,true)]
theorem der_21696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21696 :=
  CNF.rup_sound cl_21696 [cl_15742,cl_13616,cl_13595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15742 v h) (hints_cons _ _ _ (inp_13616 v h) (hints_cons _ _ _ (inp_13595 v h) (by intro d hd; cases hd))))
def cl_21824 : CNF.NClause := [(912,true),(905,true),(921,true),(915,true),(923,true),(901,true),(903,true),(926,true),(927,true),(909,true),(919,true)]
theorem der_21824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21824 :=
  CNF.rup_sound cl_21824 [cl_12754,cl_12716,cl_15716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12754 v h) (hints_cons _ _ _ (inp_12716 v h) (hints_cons _ _ _ (der_15716 v h) (by intro d hd; cases hd))))
def cl_22033 : CNF.NClause := [(1069,true),(1060,true),(1065,true),(1066,true),(1073,true),(1078,true),(1058,true),(1081,true),(1057,true),(1082,true),(1061,true),(1064,true),(1074,true)]
theorem der_22033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22033 :=
  CNF.rup_sound cl_22033 [cl_15766,cl_13656,cl_13687,cl_15717,cl_13616,cl_15758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15766 v h) (hints_cons _ _ _ (inp_13656 v h) (hints_cons _ _ _ (inp_13687 v h) (hints_cons _ _ _ (der_15717 v h) (hints_cons _ _ _ (inp_13616 v h) (hints_cons _ _ _ (der_15758 v h) (by intro d hd; cases hd)))))))
def cl_22035 : CNF.NClause := [(916,true),(910,true),(911,true),(918,true),(923,true),(901,true),(926,true),(927,true),(906,true),(909,true),(900,true)]
theorem der_22035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22035 :=
  CNF.rup_sound cl_22035 [cl_12706,cl_15669,cl_15707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12706 v h) (hints_cons _ _ _ (der_15669 v h) (hints_cons _ _ _ (der_15707 v h) (by intro d hd; cases hd))))
def cl_22077 : CNF.NClause := [(1065,true),(1076,true),(1069,true),(1059,true),(1063,true),(1068,true),(1078,true),(1056,false),(1081,true),(1057,true),(1061,true),(1074,true),(1055,true)]
theorem der_22077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22077 :=
  CNF.rup_sound cl_22077 [cl_13595,cl_13656,cl_13694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13595 v h) (hints_cons _ _ _ (inp_13656 v h) (hints_cons _ _ _ (inp_13694 v h) (by intro d hd; cases hd))))
def cl_22079 : CNF.NClause := [(1062,true),(1059,true),(1063,true),(1068,true),(1078,true),(1081,true),(1057,true),(1082,true),(1061,true),(1064,true),(1074,true),(1055,true)]
theorem der_22079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22079 :=
  CNF.rup_sound cl_22079 [cl_13634,cl_15741,cl_13600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13634 v h) (hints_cons _ _ _ (der_15741 v h) (hints_cons _ _ _ (inp_13600 v h) (by intro d hd; cases hd))))
def cl_22436 : CNF.NClause := [(1069,true),(1071,true),(1077,true),(1083,false),(1080,true),(1078,true),(1058,true),(1057,true),(1061,true),(1064,true),(1074,true)]
theorem der_22436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22436 :=
  CNF.rup_sound cl_22436 [cl_15766,cl_13656,cl_13677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15766 v h) (hints_cons _ _ _ (inp_13656 v h) (hints_cons _ _ _ (inp_13677 v h) (by intro d hd; cases hd))))
def cl_22745 : CNF.NClause := [(926,true),(922,true),(920,true),(919,true),(918,true),(917,true),(916,true),(913,true),(911,true),(909,true),(906,true),(902,true)]
theorem der_22745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22745 :=
  CNF.rup_sound cl_22745 [cl_12760,cl_15703,cl_15716,cl_15686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12760 v h) (hints_cons _ _ _ (der_15703 v h) (hints_cons _ _ _ (der_15716 v h) (hints_cons _ _ _ (der_15686 v h) (by intro d hd; cases hd)))))
def cl_22758 : CNF.NClause := [(152,true),(150,true),(128,false),(146,true),(151,true),(143,true),(142,true),(138,true),(136,true),(134,true),(131,true),(127,true),(125,true)]
theorem der_22758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22758 :=
  CNF.rup_sound cl_22758 [cl_8039,cl_15617,cl_8107,cl_8116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8039 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (inp_8107 v h) (hints_cons _ _ _ (inp_8116 v h) (by intro d hd; cases hd)))))
def cl_22826 : CNF.NClause := [(923,true),(920,false),(927,true),(925,true),(921,true),(922,true),(917,true),(916,true),(913,true),(911,true),(902,true)]
theorem der_22826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22826 :=
  CNF.rup_sound cl_22826 [cl_15715,cl_15675,cl_12667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15715 v h) (hints_cons _ _ _ (der_15675 v h) (hints_cons _ _ _ (inp_12667 v h) (by intro d hd; cases hd))))
def cl_22853 : CNF.NClause := [(151,true),(150,true),(152,false),(146,true),(145,true),(143,true),(142,true),(138,true),(136,true),(127,true),(125,true)]
theorem der_22853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22853 :=
  CNF.rup_sound cl_22853 [cl_8110,cl_15618,cl_8112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8110 v h) (hints_cons _ _ _ (der_15618 v h) (hints_cons _ _ _ (inp_8112 v h) (by intro d hd; cases hd))))
def cl_22884 : CNF.NClause := [(923,true),(925,true),(921,false),(927,true),(922,true),(920,true),(917,true),(916,true),(913,true),(911,true),(902,true)]
theorem der_22884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22884 :=
  CNF.rup_sound cl_22884 [cl_15674,cl_15715,cl_12667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15674 v h) (hints_cons _ _ _ (der_15715 v h) (hints_cons _ _ _ (inp_12667 v h) (by intro d hd; cases hd))))
def cl_22898 : CNF.NClause := [(921,true),(905,true),(923,true),(922,true),(920,true),(917,true),(916,true),(913,true),(911,true),(909,true),(906,true),(902,true),(900,true)]
theorem der_22898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22898 :=
  CNF.rup_sound cl_22898 [cl_15669,cl_15676,cl_15694,cl_12666,cl_12689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15669 v h) (hints_cons _ _ _ (der_15676 v h) (hints_cons _ _ _ (der_15694 v h) (hints_cons _ _ _ (inp_12666 v h) (hints_cons _ _ _ (inp_12689 v h) (by intro d hd; cases hd))))))
def cl_22899 : CNF.NClause := [(926,true),(901,false),(923,true),(925,true),(922,true),(920,true),(918,true),(917,true),(916,true),(913,true),(909,true),(906,true),(900,true)]
theorem der_22899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22899 :=
  CNF.rup_sound cl_22899 [cl_15703,cl_12706,cl_15686,cl_12725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15703 v h) (hints_cons _ _ _ (inp_12706 v h) (hints_cons _ _ _ (der_15686 v h) (hints_cons _ _ _ (inp_12725 v h) (by intro d hd; cases hd)))))
def cl_23157 : CNF.NClause := [(87,true),(1,false),(2,true),(4,false)]
theorem der_23157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23157 :=
  CNF.rup_sound cl_23157 [cl_15273,cl_15269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15273 v h) (hints_cons _ _ _ (der_15269 v h) (by intro d hd; cases hd)))
def cl_23158 : CNF.NClause := [(87,true),(2,true),(1,false),(3,false)]
theorem der_23158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23158 :=
  CNF.rup_sound cl_23158 [cl_15277,cl_15269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15277 v h) (hints_cons _ _ _ (der_15269 v h) (by intro d hd; cases hd)))
def chunk001 : List CNF.NClause := [cl_15491,cl_15492,cl_15493,cl_15494,cl_15495,cl_15496,cl_15497,cl_15498,cl_15499,cl_15500,cl_15501,cl_15502,cl_15503,cl_15504,cl_15505,cl_15506,cl_15507,cl_15508,cl_15509,cl_15510,cl_15511,cl_15512,cl_15513,cl_15514,cl_15515,cl_15516,cl_15517,cl_15518,cl_15519,cl_15520,cl_15521,cl_15522,cl_15523,cl_15524,cl_15525,cl_15526,cl_15527,cl_15528,cl_15529,cl_15530,cl_15531,cl_15532,cl_15533,cl_15534,cl_15535,cl_15536,cl_15537,cl_15538,cl_15539,cl_15540,cl_15541,cl_15542,cl_15543,cl_15544,cl_15545,cl_15546,cl_15547,cl_15548,cl_15549,cl_15550,cl_15551,cl_15552,cl_15553,cl_15554,cl_15555,cl_15556,cl_15557,cl_15558,cl_15559,cl_15560,cl_15561,cl_15562,cl_15563,cl_15564,cl_15565,cl_15566,cl_15567,cl_15568,cl_15569,cl_15570,cl_15571,cl_15572,cl_15573,cl_15574,cl_15575,cl_15576,cl_15577,cl_15578,cl_15579,cl_15580,cl_15581,cl_15582,cl_15583,cl_15584,cl_15585,cl_15586,cl_15587,cl_15588,cl_15589,cl_15590,cl_15591,cl_15592,cl_15593,cl_15594,cl_15595,cl_15596,cl_15597,cl_15598,cl_15599,cl_15600,cl_15601,cl_15602,cl_15603,cl_15604,cl_15605,cl_15606,cl_15607,cl_15608,cl_15609,cl_15610,cl_15611,cl_15612,cl_15613,cl_15614,cl_15615,cl_15616,cl_15617,cl_15618,cl_15619,cl_15620,cl_15621,cl_15622,cl_15623,cl_15624,cl_15625,cl_15626,cl_15627,cl_15628,cl_15629,cl_15630,cl_15631,cl_15632,cl_15633,cl_15634,cl_15635,cl_15636,cl_15637,cl_15638,cl_15639,cl_15640,cl_15641,cl_15642,cl_15643,cl_15644,cl_15645,cl_15646,cl_15647,cl_15648,cl_15649,cl_15650,cl_15651,cl_15652,cl_15653,cl_15654,cl_15655,cl_15656,cl_15657,cl_15658,cl_15659,cl_15660,cl_15661,cl_15662,cl_15663,cl_15664,cl_15665,cl_15666,cl_15667,cl_15668,cl_15669,cl_15670,cl_15671,cl_15672,cl_15673,cl_15674,cl_15675,cl_15676,cl_15677,cl_15678,cl_15679,cl_15680,cl_15681,cl_15682,cl_15683,cl_15684,cl_15685,cl_15686,cl_15687,cl_15688,cl_15689,cl_15690,cl_15691,cl_15692,cl_15693,cl_15694,cl_15695,cl_15696,cl_15697,cl_15698,cl_15699,cl_15700,cl_15701,cl_15702,cl_15703,cl_15704,cl_15705,cl_15706,cl_15707,cl_15708,cl_15709,cl_15710,cl_15711,cl_15712,cl_15713,cl_15714,cl_15715,cl_15716,cl_15717,cl_15718,cl_15719,cl_15720,cl_15721,cl_15722,cl_15723,cl_15724,cl_15725,cl_15726,cl_15727,cl_15728,cl_15729,cl_15730,cl_15731,cl_15732,cl_15733,cl_15734,cl_15735,cl_15736,cl_15737,cl_15738,cl_15739,cl_15740,cl_15741,cl_15742,cl_15743,cl_15744,cl_15745,cl_15746,cl_15747,cl_15748,cl_15749,cl_15750,cl_15751,cl_15752,cl_15753,cl_15754,cl_15755,cl_15756,cl_15757,cl_15758,cl_15759,cl_15760,cl_15761,cl_15762,cl_15763,cl_15764,cl_15765,cl_15766,cl_15767,cl_15768,cl_15769,cl_15770,cl_15771,cl_15772,cl_15773,cl_15774,cl_15775,cl_15776,cl_15777,cl_15778,cl_15779,cl_15780,cl_15781,cl_15782,cl_15783,cl_15784,cl_15785,cl_15786,cl_15787,cl_15788,cl_15789,cl_15790,cl_15791,cl_15792,cl_15793,cl_15794,cl_15795,cl_15796,cl_15797,cl_15798,cl_15799,cl_15800,cl_15801,cl_15802,cl_15803,cl_15804,cl_15805,cl_15806,cl_15807,cl_15808,cl_15809,cl_15810,cl_15811,cl_15812,cl_15813,cl_15814,cl_15815,cl_15816,cl_15817,cl_15818,cl_15819,cl_15820,cl_15821,cl_15822,cl_15823,cl_15824,cl_15825,cl_15826,cl_15827,cl_15828,cl_15829,cl_15830,cl_15831,cl_15832,cl_15833,cl_15834,cl_15835,cl_15836,cl_15837,cl_15838,cl_15839,cl_15840,cl_15841,cl_15842,cl_15843,cl_15844,cl_15845,cl_15846,cl_15847,cl_15848,cl_15849,cl_15850,cl_15851,cl_15852,cl_15853,cl_15854,cl_15855,cl_15856,cl_15857,cl_15858,cl_15859,cl_15860,cl_15861,cl_15862,cl_15863,cl_15864,cl_15865,cl_15866,cl_15867,cl_15868,cl_15869,cl_15870,cl_15871,cl_15872,cl_15873,cl_15874,cl_15875,cl_15876,cl_15877,cl_15878,cl_15879,cl_15880,cl_15881,cl_15882,cl_15883,cl_15884,cl_15885,cl_15886,cl_15887,cl_15888,cl_15889,cl_15890,cl_15891,cl_15892,cl_15893,cl_15894,cl_15895,cl_15896,cl_15897,cl_15898,cl_15899,cl_15900,cl_15901,cl_15902,cl_15903,cl_15904,cl_15905,cl_15906,cl_15907,cl_15908,cl_15909,cl_15910,cl_15911,cl_15912,cl_15913,cl_15914,cl_15915,cl_15916,cl_15917,cl_15918,cl_15919,cl_15920,cl_15921,cl_15922,cl_15923,cl_15924,cl_15925,cl_15926,cl_15927,cl_15928,cl_15929,cl_15930,cl_15931,cl_15932,cl_15933,cl_15934,cl_16140,cl_16142,cl_16144,cl_16146,cl_16162,cl_16166,cl_16178,cl_16191,cl_16193,cl_16262,cl_16816,cl_16819,cl_17148,cl_17165,cl_17409,cl_17928,cl_19260,cl_19316,cl_19535,cl_19541,cl_19574,cl_20033,cl_20225,cl_20270,cl_20273,cl_20277,cl_20313,cl_20319,cl_20327,cl_20330,cl_20341,cl_20419,cl_20516,cl_21038,cl_21087,cl_21150,cl_21276,cl_21374,cl_21487,cl_21627,cl_21696,cl_21824,cl_22033,cl_22035,cl_22077,cl_22079,cl_22436,cl_22745,cl_22758,cl_22826,cl_22853,cl_22884,cl_22898,cl_22899,cl_23157,cl_23158]
theorem chunk_sound001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk001, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_15491 v h) (hints_cons _ _ _ (der_15492 v h) (hints_cons _ _ _ (der_15493 v h) (hints_cons _ _ _ (der_15494 v h) (hints_cons _ _ _ (der_15495 v h) (hints_cons _ _ _ (der_15496 v h) (hints_cons _ _ _ (der_15497 v h) (hints_cons _ _ _ (der_15498 v h) (hints_cons _ _ _ (der_15499 v h) (hints_cons _ _ _ (der_15500 v h) (hints_cons _ _ _ (der_15501 v h) (hints_cons _ _ _ (der_15502 v h) (hints_cons _ _ _ (der_15503 v h) (hints_cons _ _ _ (der_15504 v h) (hints_cons _ _ _ (der_15505 v h) (hints_cons _ _ _ (der_15506 v h) (hints_cons _ _ _ (der_15507 v h) (hints_cons _ _ _ (der_15508 v h) (hints_cons _ _ _ (der_15509 v h) (hints_cons _ _ _ (der_15510 v h) (hints_cons _ _ _ (der_15511 v h) (hints_cons _ _ _ (der_15512 v h) (hints_cons _ _ _ (der_15513 v h) (hints_cons _ _ _ (der_15514 v h) (hints_cons _ _ _ (der_15515 v h) (hints_cons _ _ _ (der_15516 v h) (hints_cons _ _ _ (der_15517 v h) (hints_cons _ _ _ (der_15518 v h) (hints_cons _ _ _ (der_15519 v h) (hints_cons _ _ _ (der_15520 v h) (hints_cons _ _ _ (der_15521 v h) (hints_cons _ _ _ (der_15522 v h) (hints_cons _ _ _ (der_15523 v h) (hints_cons _ _ _ (der_15524 v h) (hints_cons _ _ _ (der_15525 v h) (hints_cons _ _ _ (der_15526 v h) (hints_cons _ _ _ (der_15527 v h) (hints_cons _ _ _ (der_15528 v h) (hints_cons _ _ _ (der_15529 v h) (hints_cons _ _ _ (der_15530 v h) (hints_cons _ _ _ (der_15531 v h) (hints_cons _ _ _ (der_15532 v h) (hints_cons _ _ _ (der_15533 v h) (hints_cons _ _ _ (der_15534 v h) (hints_cons _ _ _ (der_15535 v h) (hints_cons _ _ _ (der_15536 v h) (hints_cons _ _ _ (der_15537 v h) (hints_cons _ _ _ (der_15538 v h) (hints_cons _ _ _ (der_15539 v h) (hints_cons _ _ _ (der_15540 v h) (hints_cons _ _ _ (der_15541 v h) (hints_cons _ _ _ (der_15542 v h) (hints_cons _ _ _ (der_15543 v h) (hints_cons _ _ _ (der_15544 v h) (hints_cons _ _ _ (der_15545 v h) (hints_cons _ _ _ (der_15546 v h) (hints_cons _ _ _ (der_15547 v h) (hints_cons _ _ _ (der_15548 v h) (hints_cons _ _ _ (der_15549 v h) (hints_cons _ _ _ (der_15550 v h) (hints_cons _ _ _ (der_15551 v h) (hints_cons _ _ _ (der_15552 v h) (hints_cons _ _ _ (der_15553 v h) (hints_cons _ _ _ (der_15554 v h) (hints_cons _ _ _ (der_15555 v h) (hints_cons _ _ _ (der_15556 v h) (hints_cons _ _ _ (der_15557 v h) (hints_cons _ _ _ (der_15558 v h) (hints_cons _ _ _ (der_15559 v h) (hints_cons _ _ _ (der_15560 v h) (hints_cons _ _ _ (der_15561 v h) (hints_cons _ _ _ (der_15562 v h) (hints_cons _ _ _ (der_15563 v h) (hints_cons _ _ _ (der_15564 v h) (hints_cons _ _ _ (der_15565 v h) (hints_cons _ _ _ (der_15566 v h) (hints_cons _ _ _ (der_15567 v h) (hints_cons _ _ _ (der_15568 v h) (hints_cons _ _ _ (der_15569 v h) (hints_cons _ _ _ (der_15570 v h) (hints_cons _ _ _ (der_15571 v h) (hints_cons _ _ _ (der_15572 v h) (hints_cons _ _ _ (der_15573 v h) (hints_cons _ _ _ (der_15574 v h) (hints_cons _ _ _ (der_15575 v h) (hints_cons _ _ _ (der_15576 v h) (hints_cons _ _ _ (der_15577 v h) (hints_cons _ _ _ (der_15578 v h) (hints_cons _ _ _ (der_15579 v h) (hints_cons _ _ _ (der_15580 v h) (hints_cons _ _ _ (der_15581 v h) (hints_cons _ _ _ (der_15582 v h) (hints_cons _ _ _ (der_15583 v h) (hints_cons _ _ _ (der_15584 v h) (hints_cons _ _ _ (der_15585 v h) (hints_cons _ _ _ (der_15586 v h) (hints_cons _ _ _ (der_15587 v h) (hints_cons _ _ _ (der_15588 v h) (hints_cons _ _ _ (der_15589 v h) (hints_cons _ _ _ (der_15590 v h) (hints_cons _ _ _ (der_15591 v h) (hints_cons _ _ _ (der_15592 v h) (hints_cons _ _ _ (der_15593 v h) (hints_cons _ _ _ (der_15594 v h) (hints_cons _ _ _ (der_15595 v h) (hints_cons _ _ _ (der_15596 v h) (hints_cons _ _ _ (der_15597 v h) (hints_cons _ _ _ (der_15598 v h) (hints_cons _ _ _ (der_15599 v h) (hints_cons _ _ _ (der_15600 v h) (hints_cons _ _ _ (der_15601 v h) (hints_cons _ _ _ (der_15602 v h) (hints_cons _ _ _ (der_15603 v h) (hints_cons _ _ _ (der_15604 v h) (hints_cons _ _ _ (der_15605 v h) (hints_cons _ _ _ (der_15606 v h) (hints_cons _ _ _ (der_15607 v h) (hints_cons _ _ _ (der_15608 v h) (hints_cons _ _ _ (der_15609 v h) (hints_cons _ _ _ (der_15610 v h) (hints_cons _ _ _ (der_15611 v h) (hints_cons _ _ _ (der_15612 v h) (hints_cons _ _ _ (der_15613 v h) (hints_cons _ _ _ (der_15614 v h) (hints_cons _ _ _ (der_15615 v h) (hints_cons _ _ _ (der_15616 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_15618 v h) (hints_cons _ _ _ (der_15619 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_15621 v h) (hints_cons _ _ _ (der_15622 v h) (hints_cons _ _ _ (der_15623 v h) (hints_cons _ _ _ (der_15624 v h) (hints_cons _ _ _ (der_15625 v h) (hints_cons _ _ _ (der_15626 v h) (hints_cons _ _ _ (der_15627 v h) (hints_cons _ _ _ (der_15628 v h) (hints_cons _ _ _ (der_15629 v h) (hints_cons _ _ _ (der_15630 v h) (hints_cons _ _ _ (der_15631 v h) (hints_cons _ _ _ (der_15632 v h) (hints_cons _ _ _ (der_15633 v h) (hints_cons _ _ _ (der_15634 v h) (hints_cons _ _ _ (der_15635 v h) (hints_cons _ _ _ (der_15636 v h) (hints_cons _ _ _ (der_15637 v h) (hints_cons _ _ _ (der_15638 v h) (hints_cons _ _ _ (der_15639 v h) (hints_cons _ _ _ (der_15640 v h) (hints_cons _ _ _ (der_15641 v h) (hints_cons _ _ _ (der_15642 v h) (hints_cons _ _ _ (der_15643 v h) (hints_cons _ _ _ (der_15644 v h) (hints_cons _ _ _ (der_15645 v h) (hints_cons _ _ _ (der_15646 v h) (hints_cons _ _ _ (der_15647 v h) (hints_cons _ _ _ (der_15648 v h) (hints_cons _ _ _ (der_15649 v h) (hints_cons _ _ _ (der_15650 v h) (hints_cons _ _ _ (der_15651 v h) (hints_cons _ _ _ (der_15652 v h) (hints_cons _ _ _ (der_15653 v h) (hints_cons _ _ _ (der_15654 v h) (hints_cons _ _ _ (der_15655 v h) (hints_cons _ _ _ (der_15656 v h) (hints_cons _ _ _ (der_15657 v h) (hints_cons _ _ _ (der_15658 v h) (hints_cons _ _ _ (der_15659 v h) (hints_cons _ _ _ (der_15660 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15662 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15664 v h) (hints_cons _ _ _ (der_15665 v h) (hints_cons _ _ _ (der_15666 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (der_15668 v h) (hints_cons _ _ _ (der_15669 v h) (hints_cons _ _ _ (der_15670 v h) (hints_cons _ _ _ (der_15671 v h) (hints_cons _ _ _ (der_15672 v h) (hints_cons _ _ _ (der_15673 v h) (hints_cons _ _ _ (der_15674 v h) (hints_cons _ _ _ (der_15675 v h) (hints_cons _ _ _ (der_15676 v h) (hints_cons _ _ _ (der_15677 v h) (hints_cons _ _ _ (der_15678 v h) (hints_cons _ _ _ (der_15679 v h) (hints_cons _ _ _ (der_15680 v h) (hints_cons _ _ _ (der_15681 v h) (hints_cons _ _ _ (der_15682 v h) (hints_cons _ _ _ (der_15683 v h) (hints_cons _ _ _ (der_15684 v h) (hints_cons _ _ _ (der_15685 v h) (hints_cons _ _ _ (der_15686 v h) (hints_cons _ _ _ (der_15687 v h) (hints_cons _ _ _ (der_15688 v h) (hints_cons _ _ _ (der_15689 v h) (hints_cons _ _ _ (der_15690 v h) (hints_cons _ _ _ (der_15691 v h) (hints_cons _ _ _ (der_15692 v h) (hints_cons _ _ _ (der_15693 v h) (hints_cons _ _ _ (der_15694 v h) (hints_cons _ _ _ (der_15695 v h) (hints_cons _ _ _ (der_15696 v h) (hints_cons _ _ _ (der_15697 v h) (hints_cons _ _ _ (der_15698 v h) (hints_cons _ _ _ (der_15699 v h) (hints_cons _ _ _ (der_15700 v h) (hints_cons _ _ _ (der_15701 v h) (hints_cons _ _ _ (der_15702 v h) (hints_cons _ _ _ (der_15703 v h) (hints_cons _ _ _ (der_15704 v h) (hints_cons _ _ _ (der_15705 v h) (hints_cons _ _ _ (der_15706 v h) (hints_cons _ _ _ (der_15707 v h) (hints_cons _ _ _ (der_15708 v h) (hints_cons _ _ _ (der_15709 v h) (hints_cons _ _ _ (der_15710 v h) (hints_cons _ _ _ (der_15711 v h) (hints_cons _ _ _ (der_15712 v h) (hints_cons _ _ _ (der_15713 v h) (hints_cons _ _ _ (der_15714 v h) (hints_cons _ _ _ (der_15715 v h) (hints_cons _ _ _ (der_15716 v h) (hints_cons _ _ _ (der_15717 v h) (hints_cons _ _ _ (der_15718 v h) (hints_cons _ _ _ (der_15719 v h) (hints_cons _ _ _ (der_15720 v h) (hints_cons _ _ _ (der_15721 v h) (hints_cons _ _ _ (der_15722 v h) (hints_cons _ _ _ (der_15723 v h) (hints_cons _ _ _ (der_15724 v h) (hints_cons _ _ _ (der_15725 v h) (hints_cons _ _ _ (der_15726 v h) (hints_cons _ _ _ (der_15727 v h) (hints_cons _ _ _ (der_15728 v h) (hints_cons _ _ _ (der_15729 v h) (hints_cons _ _ _ (der_15730 v h) (hints_cons _ _ _ (der_15731 v h) (hints_cons _ _ _ (der_15732 v h) (hints_cons _ _ _ (der_15733 v h) (hints_cons _ _ _ (der_15734 v h) (hints_cons _ _ _ (der_15735 v h) (hints_cons _ _ _ (der_15736 v h) (hints_cons _ _ _ (der_15737 v h) (hints_cons _ _ _ (der_15738 v h) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_15740 v h) (hints_cons _ _ _ (der_15741 v h) (hints_cons _ _ _ (der_15742 v h) (hints_cons _ _ _ (der_15743 v h) (hints_cons _ _ _ (der_15744 v h) (hints_cons _ _ _ (der_15745 v h) (hints_cons _ _ _ (der_15746 v h) (hints_cons _ _ _ (der_15747 v h) (hints_cons _ _ _ (der_15748 v h) (hints_cons _ _ _ (der_15749 v h) (hints_cons _ _ _ (der_15750 v h) (hints_cons _ _ _ (der_15751 v h) (hints_cons _ _ _ (der_15752 v h) (hints_cons _ _ _ (der_15753 v h) (hints_cons _ _ _ (der_15754 v h) (hints_cons _ _ _ (der_15755 v h) (hints_cons _ _ _ (der_15756 v h) (hints_cons _ _ _ (der_15757 v h) (hints_cons _ _ _ (der_15758 v h) (hints_cons _ _ _ (der_15759 v h) (hints_cons _ _ _ (der_15760 v h) (hints_cons _ _ _ (der_15761 v h) (hints_cons _ _ _ (der_15762 v h) (hints_cons _ _ _ (der_15763 v h) (hints_cons _ _ _ (der_15764 v h) (hints_cons _ _ _ (der_15765 v h) (hints_cons _ _ _ (der_15766 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15795 v h) (hints_cons _ _ _ (der_15796 v h) (hints_cons _ _ _ (der_15797 v h) (hints_cons _ _ _ (der_15798 v h) (hints_cons _ _ _ (der_15799 v h) (hints_cons _ _ _ (der_15800 v h) (hints_cons _ _ _ (der_15801 v h) (hints_cons _ _ _ (der_15802 v h) (hints_cons _ _ _ (der_15803 v h) (hints_cons _ _ _ (der_15804 v h) (hints_cons _ _ _ (der_15805 v h) (hints_cons _ _ _ (der_15806 v h) (hints_cons _ _ _ (der_15807 v h) (hints_cons _ _ _ (der_15808 v h) (hints_cons _ _ _ (der_15809 v h) (hints_cons _ _ _ (der_15810 v h) (hints_cons _ _ _ (der_15811 v h) (hints_cons _ _ _ (der_15812 v h) (hints_cons _ _ _ (der_15813 v h) (hints_cons _ _ _ (der_15814 v h) (hints_cons _ _ _ (der_15815 v h) (hints_cons _ _ _ (der_15816 v h) (hints_cons _ _ _ (der_15817 v h) (hints_cons _ _ _ (der_15818 v h) (hints_cons _ _ _ (der_15819 v h) (hints_cons _ _ _ (der_15820 v h) (hints_cons _ _ _ (der_15821 v h) (hints_cons _ _ _ (der_15822 v h) (hints_cons _ _ _ (der_15823 v h) (hints_cons _ _ _ (der_15824 v h) (hints_cons _ _ _ (der_15825 v h) (hints_cons _ _ _ (der_15826 v h) (hints_cons _ _ _ (der_15827 v h) (hints_cons _ _ _ (der_15828 v h) (hints_cons _ _ _ (der_15829 v h) (hints_cons _ _ _ (der_15830 v h) (hints_cons _ _ _ (der_15831 v h) (hints_cons _ _ _ (der_15832 v h) (hints_cons _ _ _ (der_15833 v h) (hints_cons _ _ _ (der_15834 v h) (hints_cons _ _ _ (der_15835 v h) (hints_cons _ _ _ (der_15836 v h) (hints_cons _ _ _ (der_15837 v h) (hints_cons _ _ _ (der_15838 v h) (hints_cons _ _ _ (der_15839 v h) (hints_cons _ _ _ (der_15840 v h) (hints_cons _ _ _ (der_15841 v h) (hints_cons _ _ _ (der_15842 v h) (hints_cons _ _ _ (der_15843 v h) (hints_cons _ _ _ (der_15844 v h) (hints_cons _ _ _ (der_15845 v h) (hints_cons _ _ _ (der_15846 v h) (hints_cons _ _ _ (der_15847 v h) (hints_cons _ _ _ (der_15848 v h) (hints_cons _ _ _ (der_15849 v h) (hints_cons _ _ _ (der_15850 v h) (hints_cons _ _ _ (der_15851 v h) (hints_cons _ _ _ (der_15852 v h) (hints_cons _ _ _ (der_15853 v h) (hints_cons _ _ _ (der_15854 v h) (hints_cons _ _ _ (der_15855 v h) (hints_cons _ _ _ (der_15856 v h) (hints_cons _ _ _ (der_15857 v h) (hints_cons _ _ _ (der_15858 v h) (hints_cons _ _ _ (der_15859 v h) (hints_cons _ _ _ (der_15860 v h) (hints_cons _ _ _ (der_15861 v h) (hints_cons _ _ _ (der_15862 v h) (hints_cons _ _ _ (der_15863 v h) (hints_cons _ _ _ (der_15864 v h) (hints_cons _ _ _ (der_15865 v h) (hints_cons _ _ _ (der_15866 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_15870 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_15872 v h) (hints_cons _ _ _ (der_15873 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_15877 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_15882 v h) (hints_cons _ _ _ (der_15883 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_15888 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_15895 v h) (hints_cons _ _ _ (der_15896 v h) (hints_cons _ _ _ (der_15897 v h) (hints_cons _ _ _ (der_15898 v h) (hints_cons _ _ _ (der_15899 v h) (hints_cons _ _ _ (der_15900 v h) (hints_cons _ _ _ (der_15901 v h) (hints_cons _ _ _ (der_15902 v h) (hints_cons _ _ _ (der_15903 v h) (hints_cons _ _ _ (der_15904 v h) (hints_cons _ _ _ (der_15905 v h) (hints_cons _ _ _ (der_15906 v h) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_15908 v h) (hints_cons _ _ _ (der_15909 v h) (hints_cons _ _ _ (der_15910 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_15913 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_15915 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_15921 v h) (hints_cons _ _ _ (der_15922 v h) (hints_cons _ _ _ (der_15923 v h) (hints_cons _ _ _ (der_15924 v h) (hints_cons _ _ _ (der_15925 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (der_15927 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (der_15929 v h) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_15931 v h) (hints_cons _ _ _ (der_15932 v h) (hints_cons _ _ _ (der_15933 v h) (hints_cons _ _ _ (der_15934 v h) (hints_cons _ _ _ (der_16140 v h) (hints_cons _ _ _ (der_16142 v h) (hints_cons _ _ _ (der_16144 v h) (hints_cons _ _ _ (der_16146 v h) (hints_cons _ _ _ (der_16162 v h) (hints_cons _ _ _ (der_16166 v h) (hints_cons _ _ _ (der_16178 v h) (hints_cons _ _ _ (der_16191 v h) (hints_cons _ _ _ (der_16193 v h) (hints_cons _ _ _ (der_16262 v h) (hints_cons _ _ _ (der_16816 v h) (hints_cons _ _ _ (der_16819 v h) (hints_cons _ _ _ (der_17148 v h) (hints_cons _ _ _ (der_17165 v h) (hints_cons _ _ _ (der_17409 v h) (hints_cons _ _ _ (der_17928 v h) (hints_cons _ _ _ (der_19260 v h) (hints_cons _ _ _ (der_19316 v h) (hints_cons _ _ _ (der_19535 v h) (hints_cons _ _ _ (der_19541 v h) (hints_cons _ _ _ (der_19574 v h) (hints_cons _ _ _ (der_20033 v h) (hints_cons _ _ _ (der_20225 v h) (hints_cons _ _ _ (der_20270 v h) (hints_cons _ _ _ (der_20273 v h) (hints_cons _ _ _ (der_20277 v h) (hints_cons _ _ _ (der_20313 v h) (hints_cons _ _ _ (der_20319 v h) (hints_cons _ _ _ (der_20327 v h) (hints_cons _ _ _ (der_20330 v h) (hints_cons _ _ _ (der_20341 v h) (hints_cons _ _ _ (der_20419 v h) (hints_cons _ _ _ (der_20516 v h) (hints_cons _ _ _ (der_21038 v h) (hints_cons _ _ _ (der_21087 v h) (hints_cons _ _ _ (der_21150 v h) (hints_cons _ _ _ (der_21276 v h) (hints_cons _ _ _ (der_21374 v h) (hints_cons _ _ _ (der_21487 v h) (hints_cons _ _ _ (der_21627 v h) (hints_cons _ _ _ (der_21696 v h) (hints_cons _ _ _ (der_21824 v h) (hints_cons _ _ _ (der_22033 v h) (hints_cons _ _ _ (der_22035 v h) (hints_cons _ _ _ (der_22077 v h) (hints_cons _ _ _ (der_22079 v h) (hints_cons _ _ _ (der_22436 v h) (hints_cons _ _ _ (der_22745 v h) (hints_cons _ _ _ (der_22758 v h) (hints_cons _ _ _ (der_22826 v h) (hints_cons _ _ _ (der_22853 v h) (hints_cons _ _ _ (der_22884 v h) (hints_cons _ _ _ (der_22898 v h) (hints_cons _ _ _ (der_22899 v h) (hints_cons _ _ _ (der_23157 v h) (hints_cons _ _ _ (der_23158 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix001 := prefix000 ++ chunk001
theorem prefix_sound001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix001, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound000 v h c hc
  · exact chunk_sound001 v h c hc
end Percolation.NReplay
