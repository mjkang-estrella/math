import NReplay020
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_33427 : CNF.NClause := [(84,true),(33,false),(74,true),(64,true),(2,true),(69,false)]
theorem der_33427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33427 :=
  CNF.rup_sound cl_33427 [cl_28102,cl_33412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28102 v h) (hints_cons _ _ _ (der_33412 v h) (by intro d hd; cases hd)))
def cl_33429 : CNF.NClause := [(33,false),(79,true),(69,true),(2,true),(64,false),(87,true)]
theorem der_33429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33429 :=
  CNF.rup_sound cl_33429 [cl_28104,cl_33421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28104 v h) (hints_cons _ _ _ (der_33421 v h) (by intro d hd; cases hd)))
def cl_33430 : CNF.NClause := [(33,false),(69,true),(64,true),(79,true),(84,true),(2,false)]
theorem der_33430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33430 :=
  CNF.rup_sound cl_33430 [cl_28105,cl_33422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28105 v h) (hints_cons _ _ _ (der_33422 v h) (by intro d hd; cases hd)))
def cl_33431 : CNF.NClause := [(69,true),(33,false),(74,true),(64,true),(79,true),(84,true)]
theorem der_33431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33431 :=
  CNF.rup_sound cl_33431 [cl_28106,cl_33430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28106 v h) (hints_cons _ _ _ (der_33430 v h) (by intro d hd; cases hd)))
def cl_33432 : CNF.NClause := [(38,false),(73,false),(89,false),(7,true),(82,false),(80,false)]
theorem der_33432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33432 :=
  CNF.rup_sound cl_33432 [cl_28110,cl_28107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28110 v h) (hints_cons _ _ _ (der_28107 v h) (by intro d hd; cases hd)))
def cl_33433 : CNF.NClause := [(38,false),(71,false),(89,false),(82,false),(7,true),(80,false)]
theorem der_33433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33433 :=
  CNF.rup_sound cl_33433 [cl_28113,cl_28111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28113 v h) (hints_cons _ _ _ (der_28111 v h) (by intro d hd; cases hd)))
def cl_33434 : CNF.NClause := [(38,false),(7,true),(89,false),(64,false),(82,false),(80,false)]
theorem der_33434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33434 :=
  CNF.rup_sound cl_33434 [cl_28115,cl_28108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28115 v h) (hints_cons _ _ _ (der_28108 v h) (by intro d hd; cases hd)))
def cl_33435 : CNF.NClause := [(38,false),(64,true),(7,true),(89,false),(82,false),(80,false)]
theorem der_33435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33435 :=
  CNF.rup_sound cl_33435 [cl_28117,cl_33432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28117 v h) (hints_cons _ _ _ (der_33432 v h) (by intro d hd; cases hd)))
def cl_33436 : CNF.NClause := [(38,false),(7,true),(89,false),(64,false),(82,false),(73,false)]
theorem der_33436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33436 :=
  CNF.rup_sound cl_33436 [cl_28122,cl_28118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28122 v h) (hints_cons _ _ _ (der_28118 v h) (by intro d hd; cases hd)))
def cl_33437 : CNF.NClause := [(38,false),(64,true),(89,false),(82,false),(73,false),(7,false)]
theorem der_33437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33437 :=
  CNF.rup_sound cl_33437 [cl_28123,cl_28109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28123 v h) (hints_cons _ _ _ (der_28109 v h) (by intro d hd; cases hd)))
def cl_33438 : CNF.NClause := [(38,false),(82,false),(80,true),(64,true),(89,false),(73,false)]
theorem der_33438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33438 :=
  CNF.rup_sound cl_33438 [cl_28124,cl_28120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28124 v h) (hints_cons _ _ _ (der_28120 v h) (by intro d hd; cases hd)))
def cl_33439 : CNF.NClause := [(38,false),(64,false),(89,false),(7,true),(82,false),(71,false)]
theorem der_33439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33439 :=
  CNF.rup_sound cl_33439 [cl_28126,cl_33436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28126 v h) (hints_cons _ _ _ (der_33436 v h) (by intro d hd; cases hd)))
def cl_33440 : CNF.NClause := [(38,false),(73,true),(89,false),(82,false),(71,false),(7,false)]
theorem der_33440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33440 :=
  CNF.rup_sound cl_33440 [cl_28127,cl_28125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28127 v h) (hints_cons _ _ _ (der_28125 v h) (by intro d hd; cases hd)))
def cl_33441 : CNF.NClause := [(38,false),(64,true),(73,true),(89,false),(82,false),(71,false)]
theorem der_33441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33441 :=
  CNF.rup_sound cl_33441 [cl_28128,cl_33440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28128 v h) (hints_cons _ _ _ (der_33440 v h) (by intro d hd; cases hd)))
def cl_33442 : CNF.NClause := [(38,false),(82,false),(64,true),(89,false),(71,true),(7,false)]
theorem der_33442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33442 :=
  CNF.rup_sound cl_33442 [cl_28131,cl_28116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28131 v h) (hints_cons _ _ _ (der_28116 v h) (by intro d hd; cases hd)))
def cl_33443 : CNF.NClause := [(38,false),(82,false),(73,true),(64,true),(7,true),(89,false)]
theorem der_33443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33443 :=
  CNF.rup_sound cl_33443 [cl_28132,cl_33435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28132 v h) (hints_cons _ _ _ (der_33435 v h) (by intro d hd; cases hd)))
def cl_33444 : CNF.NClause := [(38,false),(71,false),(89,false),(7,true),(73,false),(80,false)]
theorem der_33444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33444 :=
  CNF.rup_sound cl_33444 [cl_28135,cl_28133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28135 v h) (hints_cons _ _ _ (der_28133 v h) (by intro d hd; cases hd)))
def cl_33445 : CNF.NClause := [(38,false),(71,true),(89,false),(73,false),(80,false),(7,false)]
theorem der_33445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33445 :=
  CNF.rup_sound cl_33445 [cl_28138,cl_28136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28138 v h) (hints_cons _ _ _ (der_28136 v h) (by intro d hd; cases hd)))
def cl_33446 : CNF.NClause := [(38,false),(64,true),(89,false),(73,false),(80,false),(7,true)]
theorem der_33446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33446 :=
  CNF.rup_sound cl_33446 [cl_28139,cl_33435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28139 v h) (hints_cons _ _ _ (der_33435 v h) (by intro d hd; cases hd)))
def cl_33447 : CNF.NClause := [(38,false),(80,false),(73,true),(89,false),(64,false),(71,false)]
theorem der_33447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33447 :=
  CNF.rup_sound cl_33447 [cl_28141,cl_28140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28141 v h) (hints_cons _ _ _ (der_28140 v h) (by intro d hd; cases hd)))
def cl_33448 : CNF.NClause := [(38,false),(73,true),(89,false),(71,false),(80,false),(7,false)]
theorem der_33448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33448 :=
  CNF.rup_sound cl_33448 [cl_28142,cl_28140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28142 v h) (hints_cons _ _ _ (der_28140 v h) (by intro d hd; cases hd)))
def cl_33449 : CNF.NClause := [(38,false),(80,false),(73,true),(89,false),(71,false),(7,true)]
theorem der_33449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33449 :=
  CNF.rup_sound cl_33449 [cl_28143,cl_33447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28143 v h) (hints_cons _ _ _ (der_33447 v h) (by intro d hd; cases hd)))
def cl_33450 : CNF.NClause := [(38,false),(71,true),(89,false),(64,false),(80,false),(82,true)]
theorem der_33450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33450 :=
  CNF.rup_sound cl_33450 [cl_28145,cl_28137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28145 v h) (hints_cons _ _ _ (der_28137 v h) (by intro d hd; cases hd)))
def cl_33451 : CNF.NClause := [(38,false),(73,true),(71,true),(89,false),(80,false),(82,true)]
theorem der_33451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33451 :=
  CNF.rup_sound cl_33451 [cl_28147,cl_33450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28147 v h) (hints_cons _ _ _ (der_33450 v h) (by intro d hd; cases hd)))
def cl_33452 : CNF.NClause := [(38,false),(80,true),(89,false),(71,false),(73,false),(7,false)]
theorem der_33452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33452 :=
  CNF.rup_sound cl_33452 [cl_28150,cl_28148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28150 v h) (hints_cons _ _ _ (der_28148 v h) (by intro d hd; cases hd)))
def cl_33453 : CNF.NClause := [(38,false),(71,true),(89,false),(64,false),(73,false),(7,false)]
theorem der_33453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33453 :=
  CNF.rup_sound cl_33453 [cl_28152,cl_28136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28152 v h) (hints_cons _ _ _ (der_28136 v h) (by intro d hd; cases hd)))
def cl_33454 : CNF.NClause := [(38,false),(89,false),(71,true),(80,true),(64,false),(73,false)]
theorem der_33454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33454 :=
  CNF.rup_sound cl_33454 [cl_28153,cl_33453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28153 v h) (hints_cons _ _ _ (der_33453 v h) (by intro d hd; cases hd)))
def cl_33455 : CNF.NClause := [(38,false),(73,false),(80,true),(89,false),(71,true),(7,false)]
theorem der_33455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33455 :=
  CNF.rup_sound cl_33455 [cl_28154,cl_33454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28154 v h) (hints_cons _ _ _ (der_33454 v h) (by intro d hd; cases hd)))
def cl_33456 : CNF.NClause := [(38,false),(73,false),(80,true),(89,false),(71,true),(82,true)]
theorem der_33456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33456 :=
  CNF.rup_sound cl_33456 [cl_28155,cl_33454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28155 v h) (hints_cons _ _ _ (der_33454 v h) (by intro d hd; cases hd)))
def cl_33457 : CNF.NClause := [(38,false),(73,true),(89,false),(64,false),(71,false),(7,false)]
theorem der_33457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33457 :=
  CNF.rup_sound cl_33457 [cl_28156,cl_28140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28156 v h) (hints_cons _ _ _ (der_28140 v h) (by intro d hd; cases hd)))
def cl_33458 : CNF.NClause := [(38,false),(71,false),(73,true),(89,false),(64,false),(7,true)]
theorem der_33458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33458 :=
  CNF.rup_sound cl_33458 [cl_28157,cl_33447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28157 v h) (hints_cons _ _ _ (der_33447 v h) (by intro d hd; cases hd)))
def cl_33459 : CNF.NClause := [(38,false),(73,true),(64,true),(89,false),(71,false),(7,false)]
theorem der_33459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33459 :=
  CNF.rup_sound cl_33459 [cl_28158,cl_33440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28158 v h) (hints_cons _ _ _ (der_33440 v h) (by intro d hd; cases hd)))
def cl_33460 : CNF.NClause := [(38,false),(71,false),(73,true),(80,true),(89,false),(7,true)]
theorem der_33460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33460 :=
  CNF.rup_sound cl_33460 [cl_28159,cl_33458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28159 v h) (hints_cons _ _ _ (der_33458 v h) (by intro d hd; cases hd)))
def cl_33461 : CNF.NClause := [(38,false),(71,true),(80,true),(89,false),(64,false),(7,false)]
theorem der_33461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33461 :=
  CNF.rup_sound cl_33461 [cl_28160,cl_33454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28160 v h) (hints_cons _ _ _ (der_33454 v h) (by intro d hd; cases hd)))
def cl_33462 : CNF.NClause := [(38,false),(64,false),(71,true),(89,false),(7,true),(82,true)]
theorem der_33462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33462 :=
  CNF.rup_sound cl_33462 [cl_28161,cl_33450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28161 v h) (hints_cons _ _ _ (der_33450 v h) (by intro d hd; cases hd)))
def cl_33464 : CNF.NClause := [(38,false),(71,true),(80,true),(64,true),(89,false),(82,true)]
theorem der_33464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33464 :=
  CNF.rup_sound cl_33464 [cl_28163,cl_33456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28163 v h) (hints_cons _ _ _ (der_33456 v h) (by intro d hd; cases hd)))
def cl_33465 : CNF.NClause := [(38,false),(71,false),(82,false),(7,true),(73,false),(80,false)]
theorem der_33465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33465 :=
  CNF.rup_sound cl_33465 [cl_28166,cl_28164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28166 v h) (hints_cons _ _ _ (der_28164 v h) (by intro d hd; cases hd)))
def cl_33466 : CNF.NClause := [(38,false),(80,false),(64,false),(82,false),(73,false),(7,true)]
theorem der_33466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33466 :=
  CNF.rup_sound cl_33466 [cl_28168,cl_28108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28168 v h) (hints_cons _ _ _ (der_28108 v h) (by intro d hd; cases hd)))
def cl_33467 : CNF.NClause := [(38,false),(64,true),(82,false),(73,false),(80,false),(7,false)]
theorem der_33467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33467 :=
  CNF.rup_sound cl_33467 [cl_28169,cl_28165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28169 v h) (hints_cons _ _ _ (der_28165 v h) (by intro d hd; cases hd)))
def cl_33468 : CNF.NClause := [(38,false),(80,false),(64,true),(82,false),(73,false),(7,true)]
theorem der_33468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33468 :=
  CNF.rup_sound cl_33468 [cl_28170,cl_33435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28170 v h) (hints_cons _ _ _ (der_33435 v h) (by intro d hd; cases hd)))
def cl_33469 : CNF.NClause := [(38,false),(71,false),(64,false),(7,true),(82,false),(80,false)]
theorem der_33469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33469 :=
  CNF.rup_sound cl_33469 [cl_28172,cl_33466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28172 v h) (hints_cons _ _ _ (der_33466 v h) (by intro d hd; cases hd)))
def cl_33470 : CNF.NClause := [(38,false),(64,true),(82,false),(71,false),(80,false),(7,false)]
theorem der_33470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33470 :=
  CNF.rup_sound cl_33470 [cl_28173,cl_28165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28173 v h) (hints_cons _ _ _ (der_28165 v h) (by intro d hd; cases hd)))
def cl_33471 : CNF.NClause := [(38,false),(71,false),(73,true),(82,false),(7,true),(80,false)]
theorem der_33471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33471 :=
  CNF.rup_sound cl_33471 [cl_28174,cl_33469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28174 v h) (hints_cons _ _ _ (der_33469 v h) (by intro d hd; cases hd)))
def cl_33472 : CNF.NClause := [(38,false),(80,false),(64,false),(7,true),(82,false),(89,true)]
theorem der_33472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33472 :=
  CNF.rup_sound cl_33472 [cl_28176,cl_33466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28176 v h) (hints_cons _ _ _ (der_33466 v h) (by intro d hd; cases hd)))
def cl_33473 : CNF.NClause := [(38,false),(64,true),(82,false),(80,false),(7,false),(89,true)]
theorem der_33473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33473 :=
  CNF.rup_sound cl_33473 [cl_28177,cl_33467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28177 v h) (hints_cons _ _ _ (der_33467 v h) (by intro d hd; cases hd)))
def cl_33474 : CNF.NClause := [(38,false),(82,false),(71,true),(7,true),(64,true),(80,false)]
theorem der_33474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33474 :=
  CNF.rup_sound cl_33474 [cl_28178,cl_33435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28178 v h) (hints_cons _ _ _ (der_33435 v h) (by intro d hd; cases hd)))
def cl_33475 : CNF.NClause := [(38,false),(71,false),(64,false),(7,true),(82,false),(73,false)]
theorem der_33475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33475 :=
  CNF.rup_sound cl_33475 [cl_28180,cl_28118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28180 v h) (hints_cons _ _ _ (der_28118 v h) (by intro d hd; cases hd)))
def cl_33476 : CNF.NClause := [(38,false),(64,true),(82,false),(71,false),(73,false),(7,false)]
theorem der_33476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33476 :=
  CNF.rup_sound cl_33476 [cl_28181,cl_33467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28181 v h) (hints_cons _ _ _ (der_33467 v h) (by intro d hd; cases hd)))
def cl_33477 : CNF.NClause := [(38,false),(71,false),(7,true),(82,false),(73,false),(89,true)]
theorem der_33477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33477 :=
  CNF.rup_sound cl_33477 [cl_28182,cl_33475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28182 v h) (hints_cons _ _ _ (der_33475 v h) (by intro d hd; cases hd)))
def cl_33478 : CNF.NClause := [(38,false),(80,true),(64,false),(82,false),(73,false),(7,false)]
theorem der_33478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33478 :=
  CNF.rup_sound cl_33478 [cl_28183,cl_28179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28183 v h) (hints_cons _ _ _ (der_28179 v h) (by intro d hd; cases hd)))
def cl_33479 : CNF.NClause := [(38,false),(73,false),(64,false),(7,true),(82,false),(89,true)]
theorem der_33479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33479 :=
  CNF.rup_sound cl_33479 [cl_28184,cl_33477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28184 v h) (hints_cons _ _ _ (der_33477 v h) (by intro d hd; cases hd)))
def cl_33480 : CNF.NClause := [(38,false),(73,false),(80,true),(64,true),(82,false),(7,false)]
theorem der_33480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33480 :=
  CNF.rup_sound cl_33480 [cl_28185,cl_33476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28185 v h) (hints_cons _ _ _ (der_33476 v h) (by intro d hd; cases hd)))
def cl_33481 : CNF.NClause := [(38,false),(73,false),(64,true),(82,false),(7,true),(89,true)]
theorem der_33481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33481 :=
  CNF.rup_sound cl_33481 [cl_28186,cl_33477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28186 v h) (hints_cons _ _ _ (der_33477 v h) (by intro d hd; cases hd)))
def cl_33482 : CNF.NClause := [(38,false),(73,true),(64,false),(82,false),(71,false),(7,false)]
theorem der_33482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33482 :=
  CNF.rup_sound cl_33482 [cl_28187,cl_28171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28187 v h) (hints_cons _ _ _ (der_28171 v h) (by intro d hd; cases hd)))
def cl_33483 : CNF.NClause := [(38,false),(64,false),(73,true),(80,true),(82,false),(71,false)]
theorem der_33483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33483 :=
  CNF.rup_sound cl_33483 [cl_28188,cl_33482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28188 v h) (hints_cons _ _ _ (der_33482 v h) (by intro d hd; cases hd)))
def cl_33484 : CNF.NClause := [(38,false),(64,true),(82,false),(71,false),(7,false),(89,true)]
theorem der_33484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33484 :=
  CNF.rup_sound cl_33484 [cl_28189,cl_33476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28189 v h) (hints_cons _ _ _ (der_33476 v h) (by intro d hd; cases hd)))
def cl_33485 : CNF.NClause := [(38,false),(80,true),(73,true),(7,true),(82,false),(71,false)]
theorem der_33485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33485 :=
  CNF.rup_sound cl_33485 [cl_28190,cl_33483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28190 v h) (hints_cons _ _ _ (der_33483 v h) (by intro d hd; cases hd)))
def cl_33486 : CNF.NClause := [(38,false),(82,false),(80,true),(64,false),(73,true),(7,false)]
theorem der_33486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33486 :=
  CNF.rup_sound cl_33486 [cl_28191,cl_33482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28191 v h) (hints_cons _ _ _ (der_33482 v h) (by intro d hd; cases hd)))
def cl_33487 : CNF.NClause := [(38,false),(82,false),(71,true),(64,false),(7,true),(89,true)]
theorem der_33487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33487 :=
  CNF.rup_sound cl_33487 [cl_28192,cl_33479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28192 v h) (hints_cons _ _ _ (der_33479 v h) (by intro d hd; cases hd)))
def cl_33488 : CNF.NClause := [(38,false),(73,true),(64,true),(82,false),(7,false),(89,true)]
theorem der_33488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33488 :=
  CNF.rup_sound cl_33488 [cl_28193,cl_33473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28193 v h) (hints_cons _ _ _ (der_33473 v h) (by intro d hd; cases hd)))
def cl_33489 : CNF.NClause := [(38,false),(82,false),(73,true),(71,true),(64,true),(7,true)]
theorem der_33489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33489 :=
  CNF.rup_sound cl_33489 [cl_28194,cl_33443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28194 v h) (hints_cons _ _ _ (der_33443 v h) (by intro d hd; cases hd)))
def cl_33490 : CNF.NClause := [(38,false),(71,false),(64,true),(7,true),(73,false),(80,false)]
theorem der_33490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33490 :=
  CNF.rup_sound cl_33490 [cl_28198,cl_33465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28198 v h) (hints_cons _ _ _ (der_33465 v h) (by intro d hd; cases hd)))
def cl_33491 : CNF.NClause := [(38,false),(71,true),(64,false),(73,false),(80,false),(82,true)]
theorem der_33491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33491 :=
  CNF.rup_sound cl_33491 [cl_28200,cl_33450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28200 v h) (hints_cons _ _ _ (der_33450 v h) (by intro d hd; cases hd)))
def cl_33492 : CNF.NClause := [(38,false),(73,false),(80,false),(82,true),(7,false),(89,true)]
theorem der_33492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33492 :=
  CNF.rup_sound cl_33492 [cl_28201,cl_28197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28201 v h) (hints_cons _ _ _ (der_28197 v h) (by intro d hd; cases hd)))
def cl_33493 : CNF.NClause := [(38,false),(71,true),(64,true),(73,false),(80,false),(7,true)]
theorem der_33493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33493 :=
  CNF.rup_sound cl_33493 [cl_28202,cl_33446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28202 v h) (hints_cons _ _ _ (der_33446 v h) (by intro d hd; cases hd)))
def cl_33494 : CNF.NClause := [(38,false),(73,true),(64,false),(71,false),(80,false),(7,true)]
theorem der_33494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33494 :=
  CNF.rup_sound cl_33494 [cl_28204,cl_33447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28204 v h) (hints_cons _ _ _ (der_33447 v h) (by intro d hd; cases hd)))
def cl_33495 : CNF.NClause := [(38,false),(73,true),(64,true),(71,false),(80,false),(7,false)]
theorem der_33495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33495 :=
  CNF.rup_sound cl_33495 [cl_28205,cl_33470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28205 v h) (hints_cons _ _ _ (der_33470 v h) (by intro d hd; cases hd)))
def cl_33497 : CNF.NClause := [(38,false),(73,true),(71,true),(64,false),(80,false),(82,true)]
theorem der_33497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33497 :=
  CNF.rup_sound cl_33497 [cl_28208,cl_33450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28208 v h) (hints_cons _ _ _ (der_33450 v h) (by intro d hd; cases hd)))
def cl_33498 : CNF.NClause := [(38,false),(73,true),(71,true),(80,false),(82,true),(7,false)]
theorem der_33498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33498 :=
  CNF.rup_sound cl_33498 [cl_28209,cl_33497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28209 v h) (hints_cons _ _ _ (der_33497 v h) (by intro d hd; cases hd)))
def cl_33499 : CNF.NClause := [(38,false),(89,true),(71,true),(64,true),(80,false),(7,true)]
theorem der_33499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33499 :=
  CNF.rup_sound cl_33499 [cl_28210,cl_33493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28210 v h) (hints_cons _ _ _ (der_33493 v h) (by intro d hd; cases hd)))
def cl_33500 : CNF.NClause := [(38,false),(64,true),(71,false),(73,false),(7,false),(89,true)]
theorem der_33500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33500 :=
  CNF.rup_sound cl_33500 [cl_28213,cl_33484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28213 v h) (hints_cons _ _ _ (der_33484 v h) (by intro d hd; cases hd)))
def cl_33501 : CNF.NClause := [(38,false),(82,true),(64,true),(71,false),(73,false),(7,true)]
theorem der_33501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33501 :=
  CNF.rup_sound cl_33501 [cl_28214,cl_33490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28214 v h) (hints_cons _ _ _ (der_33490 v h) (by intro d hd; cases hd)))
def cl_33502 : CNF.NClause := [(38,false),(71,true),(64,false),(73,false),(82,true),(7,false)]
theorem der_33502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33502 :=
  CNF.rup_sound cl_33502 [cl_28215,cl_33453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28215 v h) (hints_cons _ _ _ (der_33453 v h) (by intro d hd; cases hd)))
def cl_33503 : CNF.NClause := [(38,false),(73,false),(80,true),(64,false),(71,true),(82,true)]
theorem der_33503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33503 :=
  CNF.rup_sound cl_33503 [cl_28216,cl_33454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28216 v h) (hints_cons _ _ _ (der_33454 v h) (by intro d hd; cases hd)))
def cl_33505 : CNF.NClause := [(38,false),(73,false),(71,true),(64,true),(7,true),(89,true)]
theorem der_33505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33505 :=
  CNF.rup_sound cl_33505 [cl_28218,cl_33493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28218 v h) (hints_cons _ _ _ (der_33493 v h) (by intro d hd; cases hd)))
def cl_33506 : CNF.NClause := [(38,false),(73,true),(80,true),(64,false),(71,false),(7,false)]
theorem der_33506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33506 :=
  CNF.rup_sound cl_33506 [cl_28219,cl_33482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28219 v h) (hints_cons _ _ _ (der_33482 v h) (by intro d hd; cases hd)))
def cl_33507 : CNF.NClause := [(38,false),(73,true),(80,true),(64,false),(71,false),(89,true)]
theorem der_33507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33507 :=
  CNF.rup_sound cl_33507 [cl_28220,cl_33483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28220 v h) (hints_cons _ _ _ (der_33483 v h) (by intro d hd; cases hd)))
def cl_33508 : CNF.NClause := [(38,false),(73,true),(64,true),(71,false),(7,false),(89,true)]
theorem der_33508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33508 :=
  CNF.rup_sound cl_33508 [cl_28221,cl_33488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28221 v h) (hints_cons _ _ _ (der_33488 v h) (by intro d hd; cases hd)))
def cl_33509 : CNF.NClause := [(38,false),(71,true),(64,false),(82,true),(7,false),(89,true)]
theorem der_33509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33509 :=
  CNF.rup_sound cl_33509 [cl_28223,cl_33502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28223 v h) (hints_cons _ _ _ (der_33502 v h) (by intro d hd; cases hd)))
def cl_33510 : CNF.NClause := [(38,false),(73,true),(71,true),(64,false),(82,true),(89,true)]
theorem der_33510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33510 :=
  CNF.rup_sound cl_33510 [cl_28224,cl_33497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28224 v h) (hints_cons _ _ _ (der_33497 v h) (by intro d hd; cases hd)))
def cl_33511 : CNF.NClause := [(38,false),(73,true),(71,true),(64,true),(82,true),(7,false)]
theorem der_33511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33511 :=
  CNF.rup_sound cl_33511 [cl_28225,cl_33498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28225 v h) (hints_cons _ _ _ (der_33498 v h) (by intro d hd; cases hd)))
def cl_33512 : CNF.NClause := [(38,false),(64,true),(71,true),(80,true),(7,true),(89,true)]
theorem der_33512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33512 :=
  CNF.rup_sound cl_33512 [cl_28226,cl_33505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28226 v h) (hints_cons _ _ _ (der_33505 v h) (by intro d hd; cases hd)))
def cl_33513 : CNF.NClause := [(59,false),(73,false),(62,true),(90,false),(84,false),(81,false)]
theorem der_33513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33513 :=
  CNF.rup_sound cl_33513 [cl_28231,cl_28230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28231 v h) (hints_cons _ _ _ (der_28230 v h) (by intro d hd; cases hd)))
def cl_33514 : CNF.NClause := [(59,false),(70,false),(62,true),(84,false),(81,false),(28,true)]
theorem der_33514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33514 :=
  CNF.rup_sound cl_33514 [cl_28234,cl_32082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28234 v h) (hints_cons _ _ _ (der_32082 v h) (by intro d hd; cases hd)))
def cl_33515 : CNF.NClause := [(59,false),(84,false),(70,true),(90,false),(62,false),(81,false)]
theorem der_33515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33515 :=
  CNF.rup_sound cl_33515 [cl_28236,cl_28235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28236 v h) (hints_cons _ _ _ (der_28235 v h) (by intro d hd; cases hd)))
def cl_33517 : CNF.NClause := [(59,false),(62,true),(70,true),(90,false),(84,false),(81,false)]
theorem der_33517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33517 :=
  CNF.rup_sound cl_33517 [cl_28238,cl_33513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28238 v h) (hints_cons _ _ _ (der_33513 v h) (by intro d hd; cases hd)))
def cl_33518 : CNF.NClause := [(59,false),(73,false),(62,true),(28,true),(84,false),(70,false)]
theorem der_33518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33518 :=
  CNF.rup_sound cl_33518 [cl_28241,cl_26333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28241 v h) (hints_cons _ _ _ (der_26333 v h) (by intro d hd; cases hd)))
def cl_33519 : CNF.NClause := [(59,false),(73,false),(70,true),(90,false),(62,false),(84,false)]
theorem der_33519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33519 :=
  CNF.rup_sound cl_33519 [cl_28243,cl_28242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28243 v h) (hints_cons _ _ _ (der_28242 v h) (by intro d hd; cases hd)))
def cl_33520 : CNF.NClause := [(59,false),(73,false),(28,false),(90,false),(70,true),(84,false)]
theorem der_33520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33520 :=
  CNF.rup_sound cl_33520 [cl_28244,cl_33519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28244 v h) (hints_cons _ _ _ (der_33519 v h) (by intro d hd; cases hd)))
def cl_33521 : CNF.NClause := [(59,false),(73,false),(62,true),(90,false),(70,true),(84,false)]
theorem der_33521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33521 :=
  CNF.rup_sound cl_33521 [cl_28245,cl_33513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28245 v h) (hints_cons _ _ _ (der_33513 v h) (by intro d hd; cases hd)))
def cl_33522 : CNF.NClause := [(59,false),(84,false),(73,true),(90,false),(62,false),(70,false)]
theorem der_33522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33522 :=
  CNF.rup_sound cl_33522 [cl_28247,cl_28246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28247 v h) (hints_cons _ _ _ (der_28246 v h) (by intro d hd; cases hd)))
def cl_33523 : CNF.NClause := [(59,false),(84,false),(28,false),(90,false),(73,true),(70,false)]
theorem der_33523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33523 :=
  CNF.rup_sound cl_33523 [cl_28248,cl_33522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28248 v h) (hints_cons _ _ _ (der_33522 v h) (by intro d hd; cases hd)))
def cl_33524 : CNF.NClause := [(59,false),(84,false),(81,true),(90,false),(73,true),(70,false)]
theorem der_33524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33524 :=
  CNF.rup_sound cl_33524 [cl_28249,cl_33522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28249 v h) (hints_cons _ _ _ (der_33522 v h) (by intro d hd; cases hd)))
def cl_33526 : CNF.NClause := [(59,false),(62,false),(73,true),(90,false),(70,true),(84,false)]
theorem der_33526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33526 :=
  CNF.rup_sound cl_33526 [cl_28251,cl_33515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28251 v h) (hints_cons _ _ _ (der_33515 v h) (by intro d hd; cases hd)))
def cl_33527 : CNF.NClause := [(59,false),(90,false),(73,true),(28,false),(70,true),(84,false)]
theorem der_33527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33527 :=
  CNF.rup_sound cl_33527 [cl_28252,cl_33526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28252 v h) (hints_cons _ _ _ (der_33526 v h) (by intro d hd; cases hd)))
def cl_33528 : CNF.NClause := [(59,false),(84,false),(70,true),(73,true),(28,true),(90,false)]
theorem der_33528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33528 :=
  CNF.rup_sound cl_33528 [cl_28253,cl_33526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28253 v h) (hints_cons _ _ _ (der_33526 v h) (by intro d hd; cases hd)))
def cl_33529 : CNF.NClause := [(59,false),(70,false),(62,true),(73,false),(81,false),(28,true)]
theorem der_33529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33529 :=
  CNF.rup_sound cl_33529 [cl_28256,cl_32084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28256 v h) (hints_cons _ _ _ (der_32084 v h) (by intro d hd; cases hd)))
def cl_33530 : CNF.NClause := [(59,false),(81,false),(70,true),(90,false),(62,false),(73,false)]
theorem der_33530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33530 :=
  CNF.rup_sound cl_33530 [cl_28258,cl_28257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28258 v h) (hints_cons _ _ _ (der_28257 v h) (by intro d hd; cases hd)))
def cl_33531 : CNF.NClause := [(59,false),(81,false),(28,false),(90,false),(73,false),(70,true)]
theorem der_33531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33531 :=
  CNF.rup_sound cl_33531 [cl_28259,cl_33530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28259 v h) (hints_cons _ _ _ (der_33530 v h) (by intro d hd; cases hd)))
def cl_33532 : CNF.NClause := [(59,false),(81,false),(62,true),(90,false),(73,false),(70,true)]
theorem der_33532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33532 :=
  CNF.rup_sound cl_33532 [cl_28260,cl_33513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28260 v h) (hints_cons _ _ _ (der_33513 v h) (by intro d hd; cases hd)))
def cl_33533 : CNF.NClause := [(59,false),(70,false),(73,true),(90,false),(62,false),(81,false)]
theorem der_33533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33533 :=
  CNF.rup_sound cl_33533 [cl_28262,cl_28261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28262 v h) (hints_cons _ _ _ (der_28261 v h) (by intro d hd; cases hd)))
def cl_33534 : CNF.NClause := [(59,false),(70,false),(28,false),(90,false),(81,false),(73,true)]
theorem der_33534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33534 :=
  CNF.rup_sound cl_33534 [cl_28263,cl_33523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28263 v h) (hints_cons _ _ _ (der_33523 v h) (by intro d hd; cases hd)))
def cl_33535 : CNF.NClause := [(59,false),(70,false),(84,true),(90,false),(81,false),(73,true)]
theorem der_33535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33535 :=
  CNF.rup_sound cl_33535 [cl_28264,cl_33533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28264 v h) (hints_cons _ _ _ (der_33533 v h) (by intro d hd; cases hd)))
def cl_33537 : CNF.NClause := [(59,false),(81,false),(73,true),(90,false),(62,false),(70,true)]
theorem der_33537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33537 :=
  CNF.rup_sound cl_33537 [cl_28266,cl_33515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28266 v h) (hints_cons _ _ _ (der_33515 v h) (by intro d hd; cases hd)))
def cl_33538 : CNF.NClause := [(59,false),(81,false),(62,true),(28,false),(90,false),(70,true)]
theorem der_33538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33538 :=
  CNF.rup_sound cl_33538 [cl_28267,cl_33532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28267 v h) (hints_cons _ _ _ (der_33532 v h) (by intro d hd; cases hd)))
def cl_33539 : CNF.NClause := [(59,false),(81,false),(70,true),(62,true),(90,false),(28,true)]
theorem der_33539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33539 :=
  CNF.rup_sound cl_33539 [cl_28268,cl_33532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28268 v h) (hints_cons _ _ _ (der_33532 v h) (by intro d hd; cases hd)))
def cl_33540 : CNF.NClause := [(59,false),(70,false),(81,true),(90,false),(62,false),(73,false)]
theorem der_33540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33540 :=
  CNF.rup_sound cl_33540 [cl_28270,cl_28269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28270 v h) (hints_cons _ _ _ (der_28269 v h) (by intro d hd; cases hd)))
def cl_33541 : CNF.NClause := [(59,false),(70,false),(28,false),(90,false),(73,false),(62,true)]
theorem der_33541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33541 :=
  CNF.rup_sound cl_33541 [cl_28271,cl_28255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28271 v h) (hints_cons _ _ _ (der_28255 v h) (by intro d hd; cases hd)))
def cl_33542 : CNF.NClause := [(59,false),(70,false),(62,true),(81,true),(73,false),(28,true)]
theorem der_33542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33542 :=
  CNF.rup_sound cl_33542 [cl_28272,cl_32085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28272 v h) (hints_cons _ _ _ (der_32085 v h) (by intro d hd; cases hd)))
def cl_33543 : CNF.NClause := [(59,false),(62,false),(28,false),(90,false),(70,true),(73,false)]
theorem der_33543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33543 :=
  CNF.rup_sound cl_33543 [cl_28273,cl_33519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28273 v h) (hints_cons _ _ _ (der_33519 v h) (by intro d hd; cases hd)))
def cl_33544 : CNF.NClause := [(59,false),(62,false),(81,true),(90,false),(70,true),(73,false)]
theorem der_33544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33544 :=
  CNF.rup_sound cl_33544 [cl_28274,cl_33519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28274 v h) (hints_cons _ _ _ (der_33519 v h) (by intro d hd; cases hd)))
def cl_33545 : CNF.NClause := [(59,false),(90,false),(62,true),(28,false),(70,true),(73,false)]
theorem der_33545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33545 :=
  CNF.rup_sound cl_33545 [cl_28275,cl_33532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28275 v h) (hints_cons _ _ _ (der_33532 v h) (by intro d hd; cases hd)))
def cl_33546 : CNF.NClause := [(59,false),(73,false),(70,true),(62,true),(28,true),(90,false)]
theorem der_33546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33546 :=
  CNF.rup_sound cl_33546 [cl_28276,cl_33532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28276 v h) (hints_cons _ _ _ (der_33532 v h) (by intro d hd; cases hd)))
def cl_33547 : CNF.NClause := [(59,false),(62,false),(28,false),(90,false),(73,true),(70,false)]
theorem der_33547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33547 :=
  CNF.rup_sound cl_33547 [cl_28277,cl_33522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28277 v h) (hints_cons _ _ _ (der_33522 v h) (by intro d hd; cases hd)))
def cl_33548 : CNF.NClause := [(59,false),(70,false),(81,true),(90,false),(28,true),(62,false)]
theorem der_33548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33548 :=
  CNF.rup_sound cl_33548 [cl_28278,cl_33540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28278 v h) (hints_cons _ _ _ (der_33540 v h) (by intro d hd; cases hd)))
def cl_33549 : CNF.NClause := [(59,false),(90,false),(62,true),(28,false),(73,true),(70,false)]
theorem der_33549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33549 :=
  CNF.rup_sound cl_33549 [cl_28279,cl_33534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28279 v h) (hints_cons _ _ _ (der_33534 v h) (by intro d hd; cases hd)))
def cl_33550 : CNF.NClause := [(59,false),(70,false),(62,true),(81,true),(84,true),(28,true)]
theorem der_33550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33550 :=
  CNF.rup_sound cl_33550 [cl_28280,cl_32085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28280 v h) (hints_cons _ _ _ (der_32085 v h) (by intro d hd; cases hd)))
def cl_33551 : CNF.NClause := [(59,false),(90,false),(28,false),(81,true),(70,true),(62,false)]
theorem der_33551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33551 :=
  CNF.rup_sound cl_33551 [cl_28281,cl_33543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28281 v h) (hints_cons _ _ _ (der_33543 v h) (by intro d hd; cases hd)))
def cl_33552 : CNF.NClause := [(59,false),(90,false),(73,true),(81,true),(70,true),(62,false)]
theorem der_33552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33552 :=
  CNF.rup_sound cl_33552 [cl_28282,cl_33526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28282 v h) (hints_cons _ _ _ (der_33526 v h) (by intro d hd; cases hd)))
def cl_33554 : CNF.NClause := [(59,false),(84,true),(73,true),(81,true),(70,true),(90,false)]
theorem der_33554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33554 :=
  CNF.rup_sound cl_33554 [cl_28284,cl_33552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28284 v h) (hints_cons _ _ _ (der_33552 v h) (by intro d hd; cases hd)))
def cl_33555 : CNF.NClause := [(59,false),(81,false),(73,false),(84,false),(28,true),(70,false)]
theorem der_33555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33555 :=
  CNF.rup_sound cl_33555 [cl_28285,cl_28227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28285 v h) (hints_cons _ _ _ (der_28227 v h) (by intro d hd; cases hd)))
def cl_33556 : CNF.NClause := [(59,false),(73,false),(62,true),(84,false),(81,false),(70,false)]
theorem der_33556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33556 :=
  CNF.rup_sound cl_33556 [cl_28286,cl_26331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28286 v h) (hints_cons _ _ _ (der_26331 v h) (by intro d hd; cases hd)))
def cl_33557 : CNF.NClause := [(59,false),(84,false),(70,true),(62,false),(73,false),(81,false)]
theorem der_33557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33557 :=
  CNF.rup_sound cl_33557 [cl_28288,cl_28287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28288 v h) (hints_cons _ _ _ (der_28287 v h) (by intro d hd; cases hd)))
def cl_33558 : CNF.NClause := [(59,false),(70,true),(28,false),(73,false),(84,false),(81,false)]
theorem der_33558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33558 :=
  CNF.rup_sound cl_33558 [cl_28289,cl_28287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28289 v h) (hints_cons _ _ _ (der_28287 v h) (by intro d hd; cases hd)))
def cl_33559 : CNF.NClause := [(59,false),(73,false),(62,true),(28,true),(84,false),(81,false)]
theorem der_33559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33559 :=
  CNF.rup_sound cl_33559 [cl_28290,cl_33513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28290 v h) (hints_cons _ _ _ (der_33513 v h) (by intro d hd; cases hd)))
def cl_33560 : CNF.NClause := [(59,false),(73,true),(28,true),(84,false),(81,false),(70,false)]
theorem der_33560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33560 :=
  CNF.rup_sound cl_33560 [cl_28292,cl_33514] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28292 v h) (hints_cons _ _ _ (der_33514 v h) (by intro d hd; cases hd)))
def cl_33561 : CNF.NClause := [(59,false),(62,true),(28,false),(84,false),(81,false),(70,false)]
theorem der_33561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33561 :=
  CNF.rup_sound cl_33561 [cl_28293,cl_33556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28293 v h) (hints_cons _ _ _ (der_33556 v h) (by intro d hd; cases hd)))
def cl_33562 : CNF.NClause := [(59,false),(70,true),(28,false),(62,false),(84,false),(81,false)]
theorem der_33562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33562 :=
  CNF.rup_sound cl_33562 [cl_28294,cl_33557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28294 v h) (hints_cons _ _ _ (der_33557 v h) (by intro d hd; cases hd)))
def cl_33563 : CNF.NClause := [(59,false),(73,true),(70,true),(62,false),(84,false),(81,false)]
theorem der_33563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33563 :=
  CNF.rup_sound cl_33563 [cl_28295,cl_33562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28295 v h) (hints_cons _ _ _ (der_33562 v h) (by intro d hd; cases hd)))
def cl_33564 : CNF.NClause := [(59,false),(73,true),(70,true),(28,false),(84,false),(81,false)]
theorem der_33564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33564 :=
  CNF.rup_sound cl_33564 [cl_28296,cl_33562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28296 v h) (hints_cons _ _ _ (der_33562 v h) (by intro d hd; cases hd)))
def cl_33565 : CNF.NClause := [(59,false),(73,true),(70,true),(28,true),(84,false),(81,false)]
theorem der_33565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33565 :=
  CNF.rup_sound cl_33565 [cl_28297,cl_33563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28297 v h) (hints_cons _ _ _ (der_33563 v h) (by intro d hd; cases hd)))
def cl_33566 : CNF.NClause := [(59,false),(70,false),(81,true),(62,false),(73,false),(84,false)]
theorem der_33566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33566 :=
  CNF.rup_sound cl_33566 [cl_28299,cl_28298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28299 v h) (hints_cons _ _ _ (der_28298 v h) (by intro d hd; cases hd)))
def cl_33567 : CNF.NClause := [(59,false),(62,true),(28,false),(73,false),(84,false),(70,false)]
theorem der_33567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33567 :=
  CNF.rup_sound cl_33567 [cl_28300,cl_33561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28300 v h) (hints_cons _ _ _ (der_33561 v h) (by intro d hd; cases hd)))
def cl_33568 : CNF.NClause := [(59,false),(84,false),(28,false),(62,false),(73,false),(70,true)]
theorem der_33568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33568 :=
  CNF.rup_sound cl_33568 [cl_28301,cl_33519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28301 v h) (hints_cons _ _ _ (der_33519 v h) (by intro d hd; cases hd)))
def cl_33569 : CNF.NClause := [(59,false),(73,false),(70,true),(62,false),(28,true),(84,false)]
theorem der_33569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33569 :=
  CNF.rup_sound cl_33569 [cl_28302,cl_33557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28302 v h) (hints_cons _ _ _ (der_33557 v h) (by intro d hd; cases hd)))
def cl_33570 : CNF.NClause := [(59,false),(73,false),(62,true),(28,false),(81,true),(84,false)]
theorem der_33570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33570 :=
  CNF.rup_sound cl_33570 [cl_28303,cl_33567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28303 v h) (hints_cons _ _ _ (der_33567 v h) (by intro d hd; cases hd)))
def cl_33571 : CNF.NClause := [(59,false),(73,false),(70,true),(62,true),(81,true),(84,false)]
theorem der_33571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33571 :=
  CNF.rup_sound cl_33571 [cl_28304,cl_33570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28304 v h) (hints_cons _ _ _ (der_33570 v h) (by intro d hd; cases hd)))
def cl_33572 : CNF.NClause := [(59,false),(84,false),(28,false),(62,false),(73,true),(70,false)]
theorem der_33572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33572 :=
  CNF.rup_sound cl_33572 [cl_28305,cl_28291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28305 v h) (hints_cons _ _ _ (der_28291 v h) (by intro d hd; cases hd)))
def cl_33573 : CNF.NClause := [(59,false),(84,false),(73,true),(81,true),(62,false),(70,false)]
theorem der_33573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33573 :=
  CNF.rup_sound cl_33573 [cl_28306,cl_33572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28306 v h) (hints_cons _ _ _ (der_33572 v h) (by intro d hd; cases hd)))
def cl_33574 : CNF.NClause := [(59,false),(84,false),(28,false),(81,true),(73,true),(70,false)]
theorem der_33574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33574 :=
  CNF.rup_sound cl_33574 [cl_28307,cl_33573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28307 v h) (hints_cons _ _ _ (der_33573 v h) (by intro d hd; cases hd)))
def cl_33575 : CNF.NClause := [(59,false),(62,false),(73,true),(28,false),(70,true),(84,false)]
theorem der_33575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33575 :=
  CNF.rup_sound cl_33575 [cl_28308,cl_33562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28308 v h) (hints_cons _ _ _ (der_33562 v h) (by intro d hd; cases hd)))
def cl_33576 : CNF.NClause := [(59,false),(81,true),(73,true),(62,true),(28,false),(84,false)]
theorem der_33576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33576 :=
  CNF.rup_sound cl_33576 [cl_28310,cl_33574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28310 v h) (hints_cons _ _ _ (der_33574 v h) (by intro d hd; cases hd)))
def cl_33577 : CNF.NClause := [(59,false),(84,false),(73,true),(62,true),(28,true),(90,true)]
theorem der_33577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33577 :=
  CNF.rup_sound cl_33577 [cl_28311,cl_32082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28311 v h) (hints_cons _ _ _ (der_32082 v h) (by intro d hd; cases hd)))
def cl_33578 : CNF.NClause := [(59,false),(84,true),(62,false),(73,false),(81,false),(70,false)]
theorem der_33578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33578 :=
  CNF.rup_sound cl_33578 [cl_28313,cl_28254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28313 v h) (hints_cons _ _ _ (der_28254 v h) (by intro d hd; cases hd)))
def cl_33579 : CNF.NClause := [(59,false),(62,true),(28,false),(73,false),(81,false),(70,false)]
theorem der_33579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33579 :=
  CNF.rup_sound cl_33579 [cl_28314,cl_33561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28314 v h) (hints_cons _ _ _ (der_33561 v h) (by intro d hd; cases hd)))
def cl_33580 : CNF.NClause := [(59,false),(81,false),(28,false),(62,false),(73,false),(70,true)]
theorem der_33580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33580 :=
  CNF.rup_sound cl_33580 [cl_28315,cl_33562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28315 v h) (hints_cons _ _ _ (der_33562 v h) (by intro d hd; cases hd)))
def cl_33581 : CNF.NClause := [(59,false),(81,false),(70,true),(84,true),(62,false),(73,false)]
theorem der_33581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33581 :=
  CNF.rup_sound cl_33581 [cl_28316,cl_33580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28316 v h) (hints_cons _ _ _ (der_33580 v h) (by intro d hd; cases hd)))
def cl_33582 : CNF.NClause := [(59,false),(81,false),(28,false),(84,true),(73,false),(70,true)]
theorem der_33582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33582 :=
  CNF.rup_sound cl_33582 [cl_28317,cl_33580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28317 v h) (hints_cons _ _ _ (der_33580 v h) (by intro d hd; cases hd)))
def cl_33583 : CNF.NClause := [(59,false),(90,true),(70,true),(84,true),(73,false),(81,false)]
theorem der_33583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33583 :=
  CNF.rup_sound cl_33583 [cl_28318,cl_33582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28318 v h) (hints_cons _ _ _ (der_33582 v h) (by intro d hd; cases hd)))
def cl_33584 : CNF.NClause := [(59,false),(70,false),(28,false),(62,false),(81,false),(73,true)]
theorem der_33584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33584 :=
  CNF.rup_sound cl_33584 [cl_28319,cl_28291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28319 v h) (hints_cons _ _ _ (der_28291 v h) (by intro d hd; cases hd)))
def cl_33585 : CNF.NClause := [(59,false),(70,false),(73,true),(84,true),(62,false),(81,false)]
theorem der_33585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33585 :=
  CNF.rup_sound cl_33585 [cl_28320,cl_33584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28320 v h) (hints_cons _ _ _ (der_33584 v h) (by intro d hd; cases hd)))
def cl_33588 : CNF.NClause := [(59,false),(73,true),(84,true),(62,false),(81,false),(70,true)]
theorem der_33588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33588 :=
  CNF.rup_sound cl_33588 [cl_28323,cl_33537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28323 v h) (hints_cons _ _ _ (der_33537 v h) (by intro d hd; cases hd)))
def cl_33589 : CNF.NClause := [(59,false),(90,true),(73,true),(62,true),(81,false),(28,true)]
theorem der_33589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33589 :=
  CNF.rup_sound cl_33589 [cl_28325,cl_32083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28325 v h) (hints_cons _ _ _ (der_32083 v h) (by intro d hd; cases hd)))
def cl_33590 : CNF.NClause := [(59,false),(70,false),(81,true),(62,false),(73,false),(28,true)]
theorem der_33590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33590 :=
  CNF.rup_sound cl_33590 [cl_28327,cl_33566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28327 v h) (hints_cons _ _ _ (der_33566 v h) (by intro d hd; cases hd)))
def cl_33591 : CNF.NClause := [(59,false),(90,true),(81,true),(73,false),(70,false),(62,true)]
theorem der_33591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33591 :=
  CNF.rup_sound cl_33591 [cl_28328,cl_33542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28328 v h) (hints_cons _ _ _ (der_33542 v h) (by intro d hd; cases hd)))
def cl_33592 : CNF.NClause := [(59,false),(62,false),(28,false),(84,true),(70,true),(73,false)]
theorem der_33592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33592 :=
  CNF.rup_sound cl_33592 [cl_28329,cl_33582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28329 v h) (hints_cons _ _ _ (der_33582 v h) (by intro d hd; cases hd)))
def cl_33593 : CNF.NClause := [(59,false),(73,false),(70,true),(81,true),(62,false),(28,true)]
theorem der_33593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33593 :=
  CNF.rup_sound cl_33593 [cl_28330,cl_33544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28330 v h) (hints_cons _ _ _ (der_33544 v h) (by intro d hd; cases hd)))
def cl_33594 : CNF.NClause := [(59,false),(84,true),(62,true),(28,false),(70,true),(73,false)]
theorem der_33594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33594 :=
  CNF.rup_sound cl_33594 [cl_28331,cl_33582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28331 v h) (hints_cons _ _ _ (der_33582 v h) (by intro d hd; cases hd)))
def cl_33595 : CNF.NClause := [(59,false),(73,false),(62,true),(81,true),(70,true),(90,true)]
theorem der_33595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33595 :=
  CNF.rup_sound cl_33595 [cl_28332,cl_33571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28332 v h) (hints_cons _ _ _ (der_33571 v h) (by intro d hd; cases hd)))
def cl_33596 : CNF.NClause := [(59,false),(70,false),(28,false),(62,false),(73,true),(90,true)]
theorem der_33596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33596 :=
  CNF.rup_sound cl_33596 [cl_28333,cl_33584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28333 v h) (hints_cons _ _ _ (der_33584 v h) (by intro d hd; cases hd)))
def cl_33597 : CNF.NClause := [(59,false),(70,false),(73,true),(84,true),(62,false),(90,true)]
theorem der_33597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33597 :=
  CNF.rup_sound cl_33597 [cl_28334,cl_33596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28334 v h) (hints_cons _ _ _ (der_33596 v h) (by intro d hd; cases hd)))
def cl_33601 : CNF.NClause := [(59,false),(70,true),(73,true),(62,true),(28,true),(90,true)]
theorem der_33601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33601 :=
  CNF.rup_sound cl_33601 [cl_28339,cl_33577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28339 v h) (hints_cons _ _ _ (der_33577 v h) (by intro d hd; cases hd)))
def cl_33606 : CNF.NClause := [(34,false),(44,false),(49,true),(39,true),(56,true),(96,true)]
theorem der_33606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33606 :=
  CNF.rup_sound cl_33606 [cl_2219,cl_30755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2219 v h) (hints_cons _ _ _ (der_30755 v h) (by intro d hd; cases hd)))
def cl_33608 : CNF.NClause := [(49,true),(37,true),(31,true),(55,true),(57,true),(122,false)]
theorem der_33608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33608 :=
  CNF.rup_sound cl_33608 [cl_3900,cl_23811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3900 v h) (hints_cons _ _ _ (der_23811 v h) (by intro d hd; cases hd)))
def cl_33609 : CNF.NClause := [(49,true),(31,true),(43,true),(55,true),(57,true),(122,false)]
theorem der_33609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33609 :=
  CNF.rup_sound cl_33609 [cl_3902,cl_23811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3902 v h) (hints_cons _ _ _ (der_23811 v h) (by intro d hd; cases hd)))
def cl_33610 : CNF.NClause := [(39,false),(34,false),(49,true),(44,true),(56,true),(96,true)]
theorem der_33610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33610 :=
  CNF.rup_sound cl_33610 [cl_2221,cl_30117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2221 v h) (hints_cons _ _ _ (der_30117 v h) (by intro d hd; cases hd)))
def cl_33611 : CNF.NClause := [(41,false),(75,false),(72,true),(92,false),(74,false),(76,false)]
theorem der_33611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33611 :=
  CNF.rup_sound cl_33611 [cl_28344,cl_28343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28344 v h) (hints_cons _ _ _ (der_28343 v h) (by intro d hd; cases hd)))
def cl_33612 : CNF.NClause := [(41,false),(92,false),(72,true),(73,false),(75,false),(76,false)]
theorem der_33612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33612 :=
  CNF.rup_sound cl_33612 [cl_28347,cl_28346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28347 v h) (hints_cons _ _ _ (der_28346 v h) (by intro d hd; cases hd)))
def cl_33613 : CNF.NClause := [(41,false),(75,false),(73,true),(92,false),(72,false),(76,false)]
theorem der_33613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33613 :=
  CNF.rup_sound cl_33613 [cl_28349,cl_28348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28349 v h) (hints_cons _ _ _ (der_28348 v h) (by intro d hd; cases hd)))
def cl_33615 : CNF.NClause := [(41,false),(73,true),(72,true),(92,false),(75,false),(76,false)]
theorem der_33615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33615 :=
  CNF.rup_sound cl_33615 [cl_28351,cl_33611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28351 v h) (hints_cons _ _ _ (der_33611 v h) (by intro d hd; cases hd)))
def cl_33616 : CNF.NClause := [(41,false),(74,false),(72,true),(92,false),(73,false),(76,false)]
theorem der_33616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33616 :=
  CNF.rup_sound cl_33616 [cl_28354,cl_28353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28354 v h) (hints_cons _ _ _ (der_28353 v h) (by intro d hd; cases hd)))
def cl_33617 : CNF.NClause := [(41,false),(74,false),(73,true),(92,false),(72,false),(76,false)]
theorem der_33617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33617 :=
  CNF.rup_sound cl_33617 [cl_28356,cl_28355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28356 v h) (hints_cons _ _ _ (der_28355 v h) (by intro d hd; cases hd)))
def cl_33618 : CNF.NClause := [(41,false),(92,false),(73,true),(10,false),(74,false),(76,false)]
theorem der_33618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33618 :=
  CNF.rup_sound cl_33618 [cl_28357,cl_33617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28357 v h) (hints_cons _ _ _ (der_33617 v h) (by intro d hd; cases hd)))
def cl_33619 : CNF.NClause := [(41,false),(74,false),(73,true),(92,false),(10,true),(76,false)]
theorem der_33619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33619 :=
  CNF.rup_sound cl_33619 [cl_28358,cl_33617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28358 v h) (hints_cons _ _ _ (der_33617 v h) (by intro d hd; cases hd)))
def cl_33620 : CNF.NClause := [(41,false),(73,false),(74,true),(92,false),(72,false),(76,false)]
theorem der_33620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33620 :=
  CNF.rup_sound cl_33620 [cl_28360,cl_28359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28360 v h) (hints_cons _ _ _ (der_28359 v h) (by intro d hd; cases hd)))
def cl_33621 : CNF.NClause := [(41,false),(74,true),(72,true),(92,false),(73,false),(76,false)]
theorem der_33621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33621 :=
  CNF.rup_sound cl_33621 [cl_28362,cl_33612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28362 v h) (hints_cons _ _ _ (der_33612 v h) (by intro d hd; cases hd)))
def cl_33622 : CNF.NClause := [(41,false),(74,true),(73,true),(92,false),(72,false),(76,false)]
theorem der_33622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33622 :=
  CNF.rup_sound cl_33622 [cl_28364,cl_33613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28364 v h) (hints_cons _ _ _ (der_33613 v h) (by intro d hd; cases hd)))
def cl_33623 : CNF.NClause := [(41,false),(74,true),(10,false),(72,true),(92,false),(76,false)]
theorem der_33623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33623 :=
  CNF.rup_sound cl_33623 [cl_28365,cl_33621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28365 v h) (hints_cons _ _ _ (der_33621 v h) (by intro d hd; cases hd)))
def cl_33625 : CNF.NClause := [(41,false),(92,false),(72,true),(73,false),(75,false),(74,false)]
theorem der_33625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33625 :=
  CNF.rup_sound cl_33625 [cl_28369,cl_28368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28369 v h) (hints_cons _ _ _ (der_28368 v h) (by intro d hd; cases hd)))
def cl_33626 : CNF.NClause := [(41,false),(92,false),(73,true),(72,false),(75,false),(74,false)]
theorem der_33626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33626 :=
  CNF.rup_sound cl_33626 [cl_28371,cl_28370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28371 v h) (hints_cons _ _ _ (der_28370 v h) (by intro d hd; cases hd)))
def cl_33628 : CNF.NClause := [(41,false),(74,false),(72,true),(92,false),(75,false),(73,true)]
theorem der_33628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33628 :=
  CNF.rup_sound cl_33628 [cl_28373,cl_33611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28373 v h) (hints_cons _ _ _ (der_33611 v h) (by intro d hd; cases hd)))
def cl_33629 : CNF.NClause := [(41,false),(74,true),(92,false),(72,false),(73,false),(75,false)]
theorem der_33629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33629 :=
  CNF.rup_sound cl_33629 [cl_28375,cl_28374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28375 v h) (hints_cons _ _ _ (der_28374 v h) (by intro d hd; cases hd)))
def cl_33630 : CNF.NClause := [(41,false),(74,true),(72,true),(92,false),(73,false),(75,false)]
theorem der_33630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33630 :=
  CNF.rup_sound cl_33630 [cl_28377,cl_33621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28377 v h) (hints_cons _ _ _ (der_33621 v h) (by intro d hd; cases hd)))
def cl_33631 : CNF.NClause := [(41,false),(73,true),(10,false),(92,false),(72,false),(75,false)]
theorem der_33631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33631 :=
  CNF.rup_sound cl_33631 [cl_28378,cl_33613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28378 v h) (hints_cons _ _ _ (der_33613 v h) (by intro d hd; cases hd)))
def cl_33632 : CNF.NClause := [(41,false),(74,true),(73,true),(92,false),(72,false),(75,false)]
theorem der_33632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33632 :=
  CNF.rup_sound cl_33632 [cl_28379,cl_33613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28379 v h) (hints_cons _ _ _ (der_33613 v h) (by intro d hd; cases hd)))
def cl_33633 : CNF.NClause := [(41,false),(74,true),(10,false),(72,true),(92,false),(75,false)]
theorem der_33633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33633 :=
  CNF.rup_sound cl_33633 [cl_28380,cl_33630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28380 v h) (hints_cons _ _ _ (der_33630 v h) (by intro d hd; cases hd)))
def cl_33634 : CNF.NClause := [(41,false),(92,false),(74,true),(10,true),(72,true),(75,false)]
theorem der_33634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33634 :=
  CNF.rup_sound cl_33634 [cl_28381,cl_33630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28381 v h) (hints_cons _ _ _ (der_33630 v h) (by intro d hd; cases hd)))
def cl_33635 : CNF.NClause := [(41,false),(74,false),(75,true),(92,false),(72,false),(73,false)]
theorem der_33635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33635 :=
  CNF.rup_sound cl_33635 [cl_28383,cl_28382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28383 v h) (hints_cons _ _ _ (der_28382 v h) (by intro d hd; cases hd)))
def cl_33636 : CNF.NClause := [(41,false),(75,true),(10,false),(92,false),(73,false),(74,false)]
theorem der_33636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33636 :=
  CNF.rup_sound cl_33636 [cl_28384,cl_33635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28384 v h) (hints_cons _ _ _ (der_33635 v h) (by intro d hd; cases hd)))
def cl_33637 : CNF.NClause := [(41,false),(76,true),(75,true),(92,false),(73,false),(74,false)]
theorem der_33637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33637 :=
  CNF.rup_sound cl_33637 [cl_28385,cl_33635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28385 v h) (hints_cons _ _ _ (der_33635 v h) (by intro d hd; cases hd)))
def cl_33638 : CNF.NClause := [(41,false),(73,true),(10,false),(92,false),(72,false),(74,false)]
theorem der_33638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33638 :=
  CNF.rup_sound cl_33638 [cl_28386,cl_33617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28386 v h) (hints_cons _ _ _ (der_33617 v h) (by intro d hd; cases hd)))
def cl_33639 : CNF.NClause := [(41,false),(73,true),(75,true),(92,false),(72,false),(74,false)]
theorem der_33639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33639 :=
  CNF.rup_sound cl_33639 [cl_28387,cl_33617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28387 v h) (hints_cons _ _ _ (der_33617 v h) (by intro d hd; cases hd)))
def cl_33640 : CNF.NClause := [(41,false),(76,true),(75,true),(72,true),(92,false),(74,false)]
theorem der_33640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33640 :=
  CNF.rup_sound cl_33640 [cl_28389,cl_33637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28389 v h) (hints_cons _ _ _ (der_33637 v h) (by intro d hd; cases hd)))
def cl_33641 : CNF.NClause := [(41,false),(10,false),(75,true),(92,false),(72,false),(73,false)]
theorem der_33641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33641 :=
  CNF.rup_sound cl_33641 [cl_28390,cl_33635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28390 v h) (hints_cons _ _ _ (der_33635 v h) (by intro d hd; cases hd)))
def cl_33642 : CNF.NClause := [(41,false),(76,true),(75,true),(92,false),(72,false),(73,false)]
theorem der_33642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33642 :=
  CNF.rup_sound cl_33642 [cl_28391,cl_33635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28391 v h) (hints_cons _ _ _ (der_33635 v h) (by intro d hd; cases hd)))
def cl_33644 : CNF.NClause := [(41,false),(74,true),(75,true),(72,true),(92,false),(73,false)]
theorem der_33644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33644 :=
  CNF.rup_sound cl_33644 [cl_28393,cl_33621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28393 v h) (hints_cons _ _ _ (der_33621 v h) (by intro d hd; cases hd)))
def cl_33645 : CNF.NClause := [(41,false),(74,true),(73,true),(10,false),(92,false),(72,false)]
theorem der_33645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33645 :=
  CNF.rup_sound cl_33645 [cl_28394,cl_33631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28394 v h) (hints_cons _ _ _ (der_33631 v h) (by intro d hd; cases hd)))
def cl_33646 : CNF.NClause := [(41,false),(74,true),(76,true),(75,true),(92,false),(72,false)]
theorem der_33646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33646 :=
  CNF.rup_sound cl_33646 [cl_28395,cl_33642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28395 v h) (hints_cons _ _ _ (der_33642 v h) (by intro d hd; cases hd)))
def cl_33648 : CNF.NClause := [(41,false),(75,true),(74,true),(10,true),(72,true),(92,false)]
theorem der_33648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33648 :=
  CNF.rup_sound cl_33648 [cl_28397,cl_33644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28397 v h) (hints_cons _ _ _ (der_33644 v h) (by intro d hd; cases hd)))
def cl_33649 : CNF.NClause := [(41,false),(73,false),(72,true),(75,false),(74,false),(76,false)]
theorem der_33649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33649 :=
  CNF.rup_sound cl_33649 [cl_28400,cl_28399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28400 v h) (hints_cons _ _ _ (der_28399 v h) (by intro d hd; cases hd)))
def cl_33650 : CNF.NClause := [(41,false),(76,false),(73,true),(72,false),(75,false),(74,false)]
theorem der_33650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33650 :=
  CNF.rup_sound cl_33650 [cl_28402,cl_28401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28402 v h) (hints_cons _ _ _ (der_28401 v h) (by intro d hd; cases hd)))
def cl_33651 : CNF.NClause := [(41,false),(75,false),(10,false),(72,true),(74,false),(76,false)]
theorem der_33651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33651 :=
  CNF.rup_sound cl_33651 [cl_28403,cl_33649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28403 v h) (hints_cons _ _ _ (der_33649 v h) (by intro d hd; cases hd)))
def cl_33652 : CNF.NClause := [(41,false),(10,true),(72,true),(75,false),(74,false),(76,false)]
theorem der_33652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33652 :=
  CNF.rup_sound cl_33652 [cl_28404,cl_33649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28404 v h) (hints_cons _ _ _ (der_33649 v h) (by intro d hd; cases hd)))
def cl_33653 : CNF.NClause := [(41,false),(74,true),(72,false),(73,false),(75,false),(76,false)]
theorem der_33653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33653 :=
  CNF.rup_sound cl_33653 [cl_28406,cl_28405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28406 v h) (hints_cons _ _ _ (der_28405 v h) (by intro d hd; cases hd)))
def cl_33654 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(75,false),(76,false)]
theorem der_33654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33654 :=
  CNF.rup_sound cl_33654 [cl_28407,cl_33649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28407 v h) (hints_cons _ _ _ (der_33649 v h) (by intro d hd; cases hd)))
def cl_33655 : CNF.NClause := [(41,false),(73,false),(74,true),(72,true),(75,false),(76,false)]
theorem der_33655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33655 :=
  CNF.rup_sound cl_33655 [cl_28408,cl_33654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28408 v h) (hints_cons _ _ _ (der_33654 v h) (by intro d hd; cases hd)))
def cl_33656 : CNF.NClause := [(41,false),(74,true),(10,false),(72,false),(75,false),(76,false)]
theorem der_33656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33656 :=
  CNF.rup_sound cl_33656 [cl_28409,cl_28405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28409 v h) (hints_cons _ _ _ (der_28405 v h) (by intro d hd; cases hd)))
def cl_33657 : CNF.NClause := [(41,false),(74,true),(73,true),(72,false),(75,false),(76,false)]
theorem der_33657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33657 :=
  CNF.rup_sound cl_33657 [cl_28410,cl_33613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28410 v h) (hints_cons _ _ _ (der_33613 v h) (by intro d hd; cases hd)))
def cl_33658 : CNF.NClause := [(41,false),(74,true),(10,false),(72,true),(75,false),(76,false)]
theorem der_33658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33658 :=
  CNF.rup_sound cl_33658 [cl_28411,cl_33654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28411 v h) (hints_cons _ _ _ (der_33654 v h) (by intro d hd; cases hd)))
def cl_33659 : CNF.NClause := [(41,false),(75,false),(74,true),(10,true),(72,true),(76,false)]
theorem der_33659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33659 :=
  CNF.rup_sound cl_33659 [cl_28412,cl_33655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28412 v h) (hints_cons _ _ _ (der_33655 v h) (by intro d hd; cases hd)))
def cl_33660 : CNF.NClause := [(41,false),(73,false),(75,true),(72,false),(74,false),(76,false)]
theorem der_33660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33660 :=
  CNF.rup_sound cl_33660 [cl_28414,cl_28413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28414 v h) (hints_cons _ _ _ (der_28413 v h) (by intro d hd; cases hd)))
def cl_33661 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(74,false),(76,false)]
theorem der_33661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33661 :=
  CNF.rup_sound cl_33661 [cl_28415,cl_33654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28415 v h) (hints_cons _ _ _ (der_33654 v h) (by intro d hd; cases hd)))
def cl_33662 : CNF.NClause := [(41,false),(73,false),(10,true),(72,true),(74,false),(76,false)]
theorem der_33662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33662 :=
  CNF.rup_sound cl_33662 [cl_28416,cl_33649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28416 v h) (hints_cons _ _ _ (der_33649 v h) (by intro d hd; cases hd)))
def cl_33663 : CNF.NClause := [(41,false),(76,false),(10,false),(72,false),(74,false),(73,true)]
theorem der_33663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33663 :=
  CNF.rup_sound cl_33663 [cl_28417,cl_33617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28417 v h) (hints_cons _ _ _ (der_33617 v h) (by intro d hd; cases hd)))
def cl_33664 : CNF.NClause := [(41,false),(74,false),(73,true),(75,true),(72,false),(76,false)]
theorem der_33664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33664 :=
  CNF.rup_sound cl_33664 [cl_28418,cl_33663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28418 v h) (hints_cons _ _ _ (der_33663 v h) (by intro d hd; cases hd)))
def cl_33665 : CNF.NClause := [(41,false),(74,false),(73,true),(10,false),(76,false),(92,true)]
theorem der_33665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33665 :=
  CNF.rup_sound cl_33665 [cl_28419,cl_33663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28419 v h) (hints_cons _ _ _ (der_33663 v h) (by intro d hd; cases hd)))
def cl_33666 : CNF.NClause := [(41,false),(76,false),(72,true),(74,false),(10,true),(92,true)]
theorem der_33666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33666 :=
  CNF.rup_sound cl_33666 [cl_28420,cl_33652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28420 v h) (hints_cons _ _ _ (der_33652 v h) (by intro d hd; cases hd)))
def cl_33667 : CNF.NClause := [(41,false),(10,false),(75,true),(72,false),(73,false),(76,false)]
theorem der_33667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33667 :=
  CNF.rup_sound cl_33667 [cl_28421,cl_33660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28421 v h) (hints_cons _ _ _ (der_33660 v h) (by intro d hd; cases hd)))
def cl_33668 : CNF.NClause := [(41,false),(75,true),(72,false),(73,false),(76,false),(92,true)]
theorem der_33668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33668 :=
  CNF.rup_sound cl_33668 [cl_28422,cl_33660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28422 v h) (hints_cons _ _ _ (der_33660 v h) (by intro d hd; cases hd)))
def cl_33669 : CNF.NClause := [(41,false),(74,true),(10,false),(72,true),(73,false),(76,false)]
theorem der_33669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33669 :=
  CNF.rup_sound cl_33669 [cl_28423,cl_33654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28423 v h) (hints_cons _ _ _ (der_33654 v h) (by intro d hd; cases hd)))
def cl_33670 : CNF.NClause := [(41,false),(73,false),(75,true),(10,true),(76,false),(92,true)]
theorem der_33670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33670 :=
  CNF.rup_sound cl_33670 [cl_28424,cl_33668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28424 v h) (hints_cons _ _ _ (der_33668 v h) (by intro d hd; cases hd)))
def cl_33671 : CNF.NClause := [(41,false),(73,true),(10,false),(75,true),(72,false),(76,false)]
theorem der_33671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33671 :=
  CNF.rup_sound cl_33671 [cl_28425,cl_33663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28425 v h) (hints_cons _ _ _ (der_33663 v h) (by intro d hd; cases hd)))
def cl_33672 : CNF.NClause := [(41,false),(73,true),(75,true),(72,false),(76,false),(92,true)]
theorem der_33672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33672 :=
  CNF.rup_sound cl_33672 [cl_28426,cl_33664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28426 v h) (hints_cons _ _ _ (der_33664 v h) (by intro d hd; cases hd)))
def cl_33673 : CNF.NClause := [(41,false),(74,true),(10,false),(75,true),(72,true),(76,false)]
theorem der_33673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33673 :=
  CNF.rup_sound cl_33673 [cl_28427,cl_33623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28427 v h) (hints_cons _ _ _ (der_33623 v h) (by intro d hd; cases hd)))
def cl_33674 : CNF.NClause := [(41,false),(75,true),(74,true),(73,true),(72,true),(76,false)]
theorem der_33674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33674 :=
  CNF.rup_sound cl_33674 [cl_28428,cl_33673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28428 v h) (hints_cons _ _ _ (der_33673 v h) (by intro d hd; cases hd)))
def cl_33675 : CNF.NClause := [(41,false),(73,false),(76,true),(72,false),(75,false),(74,false)]
theorem der_33675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33675 :=
  CNF.rup_sound cl_33675 [cl_28430,cl_28429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28430 v h) (hints_cons _ _ _ (der_28429 v h) (by intro d hd; cases hd)))
def cl_33676 : CNF.NClause := [(41,false),(10,false),(72,true),(73,false),(75,false),(74,false)]
theorem der_33676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33676 :=
  CNF.rup_sound cl_33676 [cl_28431,cl_33654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28431 v h) (hints_cons _ _ _ (der_33654 v h) (by intro d hd; cases hd)))
def cl_33677 : CNF.NClause := [(41,false),(74,false),(76,true),(72,true),(73,false),(75,false)]
theorem der_33677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33677 :=
  CNF.rup_sound cl_33677 [cl_28432,cl_33676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28432 v h) (hints_cons _ _ _ (der_33676 v h) (by intro d hd; cases hd)))
def cl_33679 : CNF.NClause := [(41,false),(75,false),(76,true),(72,false),(10,true),(74,false)]
theorem der_33679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33679 :=
  CNF.rup_sound cl_33679 [cl_28434,cl_33675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28434 v h) (hints_cons _ _ _ (der_33675 v h) (by intro d hd; cases hd)))
def cl_33680 : CNF.NClause := [(41,false),(76,true),(10,false),(72,true),(75,false),(74,false)]
theorem der_33680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33680 :=
  CNF.rup_sound cl_33680 [cl_28435,cl_33677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28435 v h) (hints_cons _ _ _ (der_33677 v h) (by intro d hd; cases hd)))
def cl_33681 : CNF.NClause := [(41,false),(73,true),(72,true),(75,false),(74,false),(10,true)]
theorem der_33681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33681 :=
  CNF.rup_sound cl_33681 [cl_28436,cl_33628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28436 v h) (hints_cons _ _ _ (der_33628 v h) (by intro d hd; cases hd)))
def cl_33682 : CNF.NClause := [(41,false),(74,true),(10,false),(72,false),(73,false),(75,false)]
theorem der_33682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33682 :=
  CNF.rup_sound cl_33682 [cl_28437,cl_33656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28437 v h) (hints_cons _ _ _ (der_33656 v h) (by intro d hd; cases hd)))
def cl_33683 : CNF.NClause := [(41,false),(74,true),(72,false),(73,false),(75,false),(92,true)]
theorem der_33683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33683 :=
  CNF.rup_sound cl_33683 [cl_28438,cl_33653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28438 v h) (hints_cons _ _ _ (der_33653 v h) (by intro d hd; cases hd)))
def cl_33684 : CNF.NClause := [(41,false),(74,true),(10,false),(76,true),(73,false),(75,false)]
theorem der_33684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33684 :=
  CNF.rup_sound cl_33684 [cl_28439,cl_28376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28439 v h) (hints_cons _ _ _ (der_28376 v h) (by intro d hd; cases hd)))
def cl_33685 : CNF.NClause := [(41,false),(74,true),(76,true),(73,false),(75,false),(92,true)]
theorem der_33685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33685 :=
  CNF.rup_sound cl_33685 [cl_28440,cl_33684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28440 v h) (hints_cons _ _ _ (der_33684 v h) (by intro d hd; cases hd)))
def cl_33686 : CNF.NClause := [(41,false),(74,true),(10,false),(76,true),(72,false),(75,false)]
theorem der_33686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33686 :=
  CNF.rup_sound cl_33686 [cl_28441,cl_33682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28441 v h) (hints_cons _ _ _ (der_33682 v h) (by intro d hd; cases hd)))
def cl_33687 : CNF.NClause := [(41,false),(75,false),(74,true),(76,true),(72,false),(92,true)]
theorem der_33687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33687 :=
  CNF.rup_sound cl_33687 [cl_28442,cl_33686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28442 v h) (hints_cons _ _ _ (der_33686 v h) (by intro d hd; cases hd)))
def cl_33688 : CNF.NClause := [(41,false),(74,true),(10,false),(76,true),(75,false),(92,true)]
theorem der_33688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33688 :=
  CNF.rup_sound cl_33688 [cl_28443,cl_33684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28443 v h) (hints_cons _ _ _ (der_33684 v h) (by intro d hd; cases hd)))
def cl_33689 : CNF.NClause := [(41,false),(74,true),(73,true),(10,true),(72,true),(75,false)]
theorem der_33689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33689 :=
  CNF.rup_sound cl_33689 [cl_28444,cl_33659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28444 v h) (hints_cons _ _ _ (der_33659 v h) (by intro d hd; cases hd)))
def cl_33690 : CNF.NClause := [(41,false),(74,false),(75,true),(72,false),(73,false),(10,true)]
theorem der_33690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33690 :=
  CNF.rup_sound cl_33690 [cl_28446,cl_33660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28446 v h) (hints_cons _ _ _ (der_33660 v h) (by intro d hd; cases hd)))
def cl_33691 : CNF.NClause := [(41,false),(10,false),(75,true),(72,true),(73,false),(74,false)]
theorem der_33691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33691 :=
  CNF.rup_sound cl_33691 [cl_28447,cl_33661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28447 v h) (hints_cons _ _ _ (der_33661 v h) (by intro d hd; cases hd)))
def cl_33692 : CNF.NClause := [(41,false),(75,true),(92,true),(72,true),(73,false),(74,false)]
theorem der_33692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33692 :=
  CNF.rup_sound cl_33692 [cl_28448,cl_33691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28448 v h) (hints_cons _ _ _ (der_33691 v h) (by intro d hd; cases hd)))
def cl_33693 : CNF.NClause := [(41,false),(73,true),(10,false),(75,true),(72,false),(74,false)]
theorem der_33693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33693 :=
  CNF.rup_sound cl_33693 [cl_28449,cl_33663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28449 v h) (hints_cons _ _ _ (der_33663 v h) (by intro d hd; cases hd)))
def cl_33694 : CNF.NClause := [(41,false),(74,false),(75,true),(72,false),(73,true),(92,true)]
theorem der_33694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33694 :=
  CNF.rup_sound cl_33694 [cl_28450,cl_33664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28450 v h) (hints_cons _ _ _ (der_33664 v h) (by intro d hd; cases hd)))
def cl_33695 : CNF.NClause := [(41,false),(76,true),(73,true),(10,false),(75,true),(74,false)]
theorem der_33695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33695 :=
  CNF.rup_sound cl_33695 [cl_28451,cl_33693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28451 v h) (hints_cons _ _ _ (der_33693 v h) (by intro d hd; cases hd)))
def cl_33696 : CNF.NClause := [(41,false),(74,false),(73,true),(76,true),(75,true),(72,true)]
theorem der_33696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33696 :=
  CNF.rup_sound cl_33696 [cl_28452,cl_33695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28452 v h) (hints_cons _ _ _ (der_33695 v h) (by intro d hd; cases hd)))
def cl_33697 : CNF.NClause := [(41,false),(10,false),(76,true),(72,false),(73,false),(92,true)]
theorem der_33697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33697 :=
  CNF.rup_sound cl_33697 [cl_28453,cl_28445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28453 v h) (hints_cons _ _ _ (der_28445 v h) (by intro d hd; cases hd)))
def cl_33698 : CNF.NClause := [(41,false),(74,true),(92,true),(76,true),(72,false),(73,false)]
theorem der_33698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33698 :=
  CNF.rup_sound cl_33698 [cl_28454,cl_33697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28454 v h) (hints_cons _ _ _ (der_33697 v h) (by intro d hd; cases hd)))
def cl_33699 : CNF.NClause := [(41,false),(74,true),(10,false),(75,true),(72,true),(73,false)]
theorem der_33699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33699 :=
  CNF.rup_sound cl_33699 [cl_28455,cl_33669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28455 v h) (hints_cons _ _ _ (der_33669 v h) (by intro d hd; cases hd)))
def cl_33700 : CNF.NClause := [(41,false),(73,false),(74,true),(76,true),(75,true),(72,true)]
theorem der_33700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33700 :=
  CNF.rup_sound cl_33700 [cl_28456,cl_33699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28456 v h) (hints_cons _ _ _ (der_33699 v h) (by intro d hd; cases hd)))
def cl_33701 : CNF.NClause := [(41,false),(75,true),(10,false),(73,true),(72,false),(92,true)]
theorem der_33701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33701 :=
  CNF.rup_sound cl_33701 [cl_28457,cl_33671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28457 v h) (hints_cons _ _ _ (der_33671 v h) (by intro d hd; cases hd)))
def cl_33702 : CNF.NClause := [(41,false),(75,true),(74,true),(76,true),(10,true),(72,false)]
theorem der_33702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33702 :=
  CNF.rup_sound cl_33702 [cl_28458,cl_33646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28458 v h) (hints_cons _ _ _ (der_33646 v h) (by intro d hd; cases hd)))
def cl_33704 : CNF.NClause := [(41,false),(75,true),(74,true),(76,true),(10,true),(72,true)]
theorem der_33704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33704 :=
  CNF.rup_sound cl_33704 [cl_28460,cl_33648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28460 v h) (hints_cons _ _ _ (der_33648 v h) (by intro d hd; cases hd)))
def cl_33709 : CNF.NClause := [(35,false),(73,false),(63,true),(87,false),(78,false),(83,false)]
theorem der_33709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33709 :=
  CNF.rup_sound cl_33709 [cl_28465,cl_28464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28465 v h) (hints_cons _ _ _ (der_28464 v h) (by intro d hd; cases hd)))
def cl_33710 : CNF.NClause := [(35,false),(63,true),(87,false),(78,false),(83,false),(68,false)]
theorem der_33710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33710 :=
  CNF.rup_sound cl_33710 [cl_28468,cl_28467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28468 v h) (hints_cons _ _ _ (der_28467 v h) (by intro d hd; cases hd)))
def cl_33711 : CNF.NClause := [(35,false),(68,true),(63,false),(87,false),(78,false),(83,false)]
theorem der_33711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33711 :=
  CNF.rup_sound cl_33711 [cl_28470,cl_28469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28470 v h) (hints_cons _ _ _ (der_28469 v h) (by intro d hd; cases hd)))
def cl_33713 : CNF.NClause := [(35,false),(68,true),(63,true),(87,false),(78,false),(83,false)]
theorem der_33713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33713 :=
  CNF.rup_sound cl_33713 [cl_28472,cl_33709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28472 v h) (hints_cons _ _ _ (der_33709 v h) (by intro d hd; cases hd)))
def cl_33714 : CNF.NClause := [(35,false),(63,true),(87,false),(73,false),(83,false),(68,false)]
theorem der_33714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33714 :=
  CNF.rup_sound cl_33714 [cl_28475,cl_28474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28475 v h) (hints_cons _ _ _ (der_28474 v h) (by intro d hd; cases hd)))
def cl_33715 : CNF.NClause := [(35,false),(68,true),(63,false),(87,false),(73,false),(83,false)]
theorem der_33715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33715 :=
  CNF.rup_sound cl_33715 [cl_28477,cl_28476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28477 v h) (hints_cons _ _ _ (der_28476 v h) (by intro d hd; cases hd)))
def cl_33717 : CNF.NClause := [(35,false),(68,true),(63,true),(87,false),(73,false),(83,false)]
theorem der_33717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33717 :=
  CNF.rup_sound cl_33717 [cl_28479,cl_33709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28479 v h) (hints_cons _ _ _ (der_33709 v h) (by intro d hd; cases hd)))
def cl_33718 : CNF.NClause := [(35,false),(83,false),(73,true),(63,false),(87,false),(68,false)]
theorem der_33718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33718 :=
  CNF.rup_sound cl_33718 [cl_28481,cl_28480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28481 v h) (hints_cons _ _ _ (der_28480 v h) (by intro d hd; cases hd)))
def cl_33720 : CNF.NClause := [(35,false),(83,false),(63,true),(87,false),(73,true),(68,false)]
theorem der_33720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33720 :=
  CNF.rup_sound cl_33720 [cl_28483,cl_33710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28483 v h) (hints_cons _ _ _ (der_33710 v h) (by intro d hd; cases hd)))
def cl_33723 : CNF.NClause := [(35,false),(68,true),(4,false),(63,true),(87,false),(83,false)]
theorem der_33723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33723 :=
  CNF.rup_sound cl_33723 [cl_28486,cl_33717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28486 v h) (hints_cons _ _ _ (der_33717 v h) (by intro d hd; cases hd)))
def cl_33724 : CNF.NClause := [(35,false),(83,false),(68,true),(63,true),(4,true),(87,false)]
theorem der_33724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33724 :=
  CNF.rup_sound cl_33724 [cl_28487,cl_33717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28487 v h) (hints_cons _ _ _ (der_33717 v h) (by intro d hd; cases hd)))
def cl_33725 : CNF.NClause := [(35,false),(68,false),(63,true),(87,false),(78,false),(73,false)]
theorem der_33725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33725 :=
  CNF.rup_sound cl_33725 [cl_28490,cl_28489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28490 v h) (hints_cons _ _ _ (der_28489 v h) (by intro d hd; cases hd)))
def cl_33726 : CNF.NClause := [(35,false),(73,false),(68,true),(63,false),(87,false),(78,false)]
theorem der_33726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33726 :=
  CNF.rup_sound cl_33726 [cl_28492,cl_28491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28492 v h) (hints_cons _ _ _ (der_28491 v h) (by intro d hd; cases hd)))
def cl_33727 : CNF.NClause := [(35,false),(4,false),(63,true),(87,false),(78,false),(73,false)]
theorem der_33727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33727 :=
  CNF.rup_sound cl_33727 [cl_28493,cl_28489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28493 v h) (hints_cons _ _ _ (der_28489 v h) (by intro d hd; cases hd)))
def cl_33728 : CNF.NClause := [(35,false),(73,false),(68,true),(87,false),(78,false),(4,true)]
theorem der_33728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33728 :=
  CNF.rup_sound cl_33728 [cl_28494,cl_33726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28494 v h) (hints_cons _ _ _ (der_33726 v h) (by intro d hd; cases hd)))
def cl_33729 : CNF.NClause := [(35,false),(68,false),(73,true),(63,false),(87,false),(78,false)]
theorem der_33729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33729 :=
  CNF.rup_sound cl_33729 [cl_28496,cl_28495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28496 v h) (hints_cons _ _ _ (der_28495 v h) (by intro d hd; cases hd)))
def cl_33730 : CNF.NClause := [(35,false),(63,true),(87,false),(78,false),(68,false),(73,true)]
theorem der_33730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33730 :=
  CNF.rup_sound cl_33730 [cl_28498,cl_33710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28498 v h) (hints_cons _ _ _ (der_33710 v h) (by intro d hd; cases hd)))
def cl_33731 : CNF.NClause := [(35,false),(68,true),(63,false),(87,false),(78,false),(73,true)]
theorem der_33731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33731 :=
  CNF.rup_sound cl_33731 [cl_28500,cl_33711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28500 v h) (hints_cons _ _ _ (der_33711 v h) (by intro d hd; cases hd)))
def cl_33732 : CNF.NClause := [(35,false),(78,false),(68,true),(4,false),(87,false),(73,true)]
theorem der_33732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33732 :=
  CNF.rup_sound cl_33732 [cl_28501,cl_33731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28501 v h) (hints_cons _ _ _ (der_33731 v h) (by intro d hd; cases hd)))
def cl_33733 : CNF.NClause := [(35,false),(78,false),(73,true),(68,true),(87,false),(4,true)]
theorem der_33733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33733 :=
  CNF.rup_sound cl_33733 [cl_28502,cl_33731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28502 v h) (hints_cons _ _ _ (der_33731 v h) (by intro d hd; cases hd)))
def cl_33734 : CNF.NClause := [(35,false),(68,false),(78,true),(63,false),(87,false),(73,false)]
theorem der_33734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33734 :=
  CNF.rup_sound cl_33734 [cl_28504,cl_28503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28504 v h) (hints_cons _ _ _ (der_28503 v h) (by intro d hd; cases hd)))
def cl_33736 : CNF.NClause := [(35,false),(78,true),(63,true),(87,false),(73,false),(68,false)]
theorem der_33736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33736 :=
  CNF.rup_sound cl_33736 [cl_28506,cl_33714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28506 v h) (hints_cons _ _ _ (der_33714 v h) (by intro d hd; cases hd)))
def cl_33738 : CNF.NClause := [(35,false),(78,true),(68,true),(63,false),(87,false),(73,false)]
theorem der_33738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33738 :=
  CNF.rup_sound cl_33738 [cl_28508,cl_33715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28508 v h) (hints_cons _ _ _ (der_33715 v h) (by intro d hd; cases hd)))
def cl_33739 : CNF.NClause := [(35,false),(78,true),(4,false),(63,true),(87,false),(73,false)]
theorem der_33739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33739 :=
  CNF.rup_sound cl_33739 [cl_28509,cl_33736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28509 v h) (hints_cons _ _ _ (der_33736 v h) (by intro d hd; cases hd)))
def cl_33740 : CNF.NClause := [(35,false),(73,false),(78,true),(63,true),(4,true),(87,false)]
theorem der_33740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33740 :=
  CNF.rup_sound cl_33740 [cl_28510,cl_33736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28510 v h) (hints_cons _ _ _ (der_33736 v h) (by intro d hd; cases hd)))
def cl_33741 : CNF.NClause := [(35,false),(73,true),(4,false),(63,false),(87,false),(68,false)]
theorem der_33741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33741 :=
  CNF.rup_sound cl_33741 [cl_28511,cl_33718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28511 v h) (hints_cons _ _ _ (der_33718 v h) (by intro d hd; cases hd)))
def cl_33742 : CNF.NClause := [(35,false),(73,true),(68,false),(78,true),(63,false),(87,false)]
theorem der_33742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33742 :=
  CNF.rup_sound cl_33742 [cl_28512,cl_33741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28512 v h) (hints_cons _ _ _ (der_33741 v h) (by intro d hd; cases hd)))
def cl_33743 : CNF.NClause := [(35,false),(73,true),(78,true),(4,false),(87,false),(68,false)]
theorem der_33743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33743 :=
  CNF.rup_sound cl_33743 [cl_28513,cl_33741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28513 v h) (hints_cons _ _ _ (der_33741 v h) (by intro d hd; cases hd)))
def cl_33744 : CNF.NClause := [(35,false),(68,false),(78,true),(63,true),(4,true),(87,false)]
theorem der_33744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33744 :=
  CNF.rup_sound cl_33744 [cl_28514,cl_33736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28514 v h) (hints_cons _ _ _ (der_33736 v h) (by intro d hd; cases hd)))
def cl_33748 : CNF.NClause := [(35,false),(78,false),(4,true),(73,false),(83,false),(68,false)]
theorem der_33748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33748 :=
  CNF.rup_sound cl_33748 [cl_28519,cl_26324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28519 v h) (hints_cons _ _ _ (der_26324 v h) (by intro d hd; cases hd)))
def cl_33749 : CNF.NClause := [(35,false),(78,false),(63,true),(73,false),(83,false),(68,false)]
theorem der_33749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33749 :=
  CNF.rup_sound cl_33749 [cl_28520,cl_26324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28520 v h) (hints_cons _ _ _ (der_26324 v h) (by intro d hd; cases hd)))
def cl_33750 : CNF.NClause := [(35,false),(73,false),(68,true),(63,false),(78,false),(83,false)]
theorem der_33750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33750 :=
  CNF.rup_sound cl_33750 [cl_28522,cl_28521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28522 v h) (hints_cons _ _ _ (der_28521 v h) (by intro d hd; cases hd)))
def cl_33751 : CNF.NClause := [(35,false),(68,true),(4,false),(78,false),(73,false),(83,false)]
theorem der_33751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33751 :=
  CNF.rup_sound cl_33751 [cl_28523,cl_28521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28523 v h) (hints_cons _ _ _ (der_28521 v h) (by intro d hd; cases hd)))
def cl_33752 : CNF.NClause := [(35,false),(73,false),(63,true),(78,false),(4,true),(83,false)]
theorem der_33752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33752 :=
  CNF.rup_sound cl_33752 [cl_28524,cl_26324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28524 v h) (hints_cons _ _ _ (der_26324 v h) (by intro d hd; cases hd)))
def cl_33753 : CNF.NClause := [(35,false),(4,true),(63,false),(78,false),(83,false),(68,false)]
theorem der_33753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33753 :=
  CNF.rup_sound cl_33753 [cl_28526,cl_33748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28526 v h) (hints_cons _ _ _ (der_33748 v h) (by intro d hd; cases hd)))
def cl_33754 : CNF.NClause := [(35,false),(78,false),(73,true),(83,false),(68,false),(87,true)]
theorem der_33754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33754 :=
  CNF.rup_sound cl_33754 [cl_28528,cl_28527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28528 v h) (hints_cons _ _ _ (der_28527 v h) (by intro d hd; cases hd)))
def cl_33755 : CNF.NClause := [(35,false),(63,false),(68,true),(4,false),(78,false),(83,false)]
theorem der_33755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33755 :=
  CNF.rup_sound cl_33755 [cl_28529,cl_28521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28529 v h) (hints_cons _ _ _ (der_28521 v h) (by intro d hd; cases hd)))
def cl_33756 : CNF.NClause := [(35,false),(78,false),(68,true),(4,false),(63,true),(83,false)]
theorem der_33756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33756 :=
  CNF.rup_sound cl_33756 [cl_28531,cl_33751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28531 v h) (hints_cons _ _ _ (der_33751 v h) (by intro d hd; cases hd)))
def cl_33757 : CNF.NClause := [(35,false),(78,false),(73,true),(68,true),(63,true),(83,false)]
theorem der_33757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33757 :=
  CNF.rup_sound cl_33757 [cl_28532,cl_33756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28532 v h) (hints_cons _ _ _ (der_33756 v h) (by intro d hd; cases hd)))
def cl_33759 : CNF.NClause := [(35,false),(78,true),(4,false),(73,false),(83,false),(68,false)]
theorem der_33759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33759 :=
  CNF.rup_sound cl_33759 [cl_28535,cl_28533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28535 v h) (hints_cons _ _ _ (der_28533 v h) (by intro d hd; cases hd)))
def cl_33760 : CNF.NClause := [(35,false),(78,true),(87,true),(73,false),(83,false),(68,false)]
theorem der_33760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33760 :=
  CNF.rup_sound cl_33760 [cl_28536,cl_33759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28536 v h) (hints_cons _ _ _ (der_33759 v h) (by intro d hd; cases hd)))
def cl_33761 : CNF.NClause := [(35,false),(78,true),(4,false),(63,false),(73,false),(83,false)]
theorem der_33761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33761 :=
  CNF.rup_sound cl_33761 [cl_28537,cl_33759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28537 v h) (hints_cons _ _ _ (der_33759 v h) (by intro d hd; cases hd)))
def cl_33762 : CNF.NClause := [(35,false),(78,true),(87,true),(63,false),(73,false),(83,false)]
theorem der_33762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33762 :=
  CNF.rup_sound cl_33762 [cl_28538,cl_33761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28538 v h) (hints_cons _ _ _ (der_33761 v h) (by intro d hd; cases hd)))
def cl_33763 : CNF.NClause := [(35,false),(78,true),(4,false),(63,true),(73,false),(83,false)]
theorem der_33763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33763 :=
  CNF.rup_sound cl_33763 [cl_28539,cl_33759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28539 v h) (hints_cons _ _ _ (der_33759 v h) (by intro d hd; cases hd)))
def cl_33765 : CNF.NClause := [(35,false),(68,false),(73,true),(63,false),(83,false),(4,true)]
theorem der_33765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33765 :=
  CNF.rup_sound cl_33765 [cl_28542,cl_33718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28542 v h) (hints_cons _ _ _ (der_33718 v h) (by intro d hd; cases hd)))
def cl_33766 : CNF.NClause := [(35,false),(83,false),(78,true),(4,false),(63,true),(68,false)]
theorem der_33766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33766 :=
  CNF.rup_sound cl_33766 [cl_28543,cl_33759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28543 v h) (hints_cons _ _ _ (der_33759 v h) (by intro d hd; cases hd)))
def cl_33767 : CNF.NClause := [(35,false),(83,false),(73,true),(78,true),(4,true),(68,false)]
theorem der_33767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33767 :=
  CNF.rup_sound cl_33767 [cl_28544,cl_33765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28544 v h) (hints_cons _ _ _ (der_33765 v h) (by intro d hd; cases hd)))
def cl_33768 : CNF.NClause := [(35,false),(78,true),(68,true),(4,false),(63,false),(83,false)]
theorem der_33768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33768 :=
  CNF.rup_sound cl_33768 [cl_28545,cl_33761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28545 v h) (hints_cons _ _ _ (der_33761 v h) (by intro d hd; cases hd)))
def cl_33769 : CNF.NClause := [(35,false),(83,false),(73,true),(78,true),(68,true),(63,false)]
theorem der_33769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33769 :=
  CNF.rup_sound cl_33769 [cl_28546,cl_33768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28546 v h) (hints_cons _ _ _ (der_33768 v h) (by intro d hd; cases hd)))
def cl_33770 : CNF.NClause := [(35,false),(83,false),(78,true),(4,false),(63,true),(87,true)]
theorem der_33770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33770 :=
  CNF.rup_sound cl_33770 [cl_28547,cl_33763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28547 v h) (hints_cons _ _ _ (der_33763 v h) (by intro d hd; cases hd)))
def cl_33771 : CNF.NClause := [(35,false),(83,false),(78,true),(68,true),(63,true),(87,true)]
theorem der_33771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33771 :=
  CNF.rup_sound cl_33771 [cl_28548,cl_33770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28548 v h) (hints_cons _ _ _ (der_33770 v h) (by intro d hd; cases hd)))
def cl_33772 : CNF.NClause := [(35,false),(83,true),(63,false),(78,false),(73,false),(68,false)]
theorem der_33772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33772 :=
  CNF.rup_sound cl_33772 [cl_28550,cl_28549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28550 v h) (hints_cons _ _ _ (der_28549 v h) (by intro d hd; cases hd)))
def cl_33773 : CNF.NClause := [(35,false),(63,true),(78,false),(73,false),(68,false),(4,false)]
theorem der_33773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33773 :=
  CNF.rup_sound cl_33773 [cl_28551,cl_33725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28551 v h) (hints_cons _ _ _ (der_33725 v h) (by intro d hd; cases hd)))
def cl_33774 : CNF.NClause := [(35,false),(63,true),(78,false),(73,false),(68,false),(4,true)]
theorem der_33774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33774 :=
  CNF.rup_sound cl_33774 [cl_28552,cl_33725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28552 v h) (hints_cons _ _ _ (der_33725 v h) (by intro d hd; cases hd)))
def cl_33775 : CNF.NClause := [(35,false),(63,false),(87,true),(78,false),(73,false),(83,true)]
theorem der_33775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33775 :=
  CNF.rup_sound cl_33775 [cl_28554,cl_28553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28554 v h) (hints_cons _ _ _ (der_28553 v h) (by intro d hd; cases hd)))
def cl_33776 : CNF.NClause := [(35,false),(68,true),(4,false),(63,true),(78,false),(73,false)]
theorem der_33776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33776 :=
  CNF.rup_sound cl_33776 [cl_28555,cl_33727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28555 v h) (hints_cons _ _ _ (der_33727 v h) (by intro d hd; cases hd)))
def cl_33777 : CNF.NClause := [(35,false),(68,true),(78,false),(73,false),(83,true),(4,true)]
theorem der_33777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33777 :=
  CNF.rup_sound cl_33777 [cl_28556,cl_33728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28556 v h) (hints_cons _ _ _ (der_33728 v h) (by intro d hd; cases hd)))
def cl_33778 : CNF.NClause := [(35,false),(4,false),(63,false),(78,false),(68,false),(73,true)]
theorem der_33778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33778 :=
  CNF.rup_sound cl_33778 [cl_28557,cl_28525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28557 v h) (hints_cons _ _ _ (der_28525 v h) (by intro d hd; cases hd)))
def cl_33779 : CNF.NClause := [(35,false),(73,true),(63,false),(78,false),(68,false),(4,true)]
theorem der_33779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33779 :=
  CNF.rup_sound cl_33779 [cl_28558,cl_33729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28558 v h) (hints_cons _ _ _ (der_33729 v h) (by intro d hd; cases hd)))
def cl_33780 : CNF.NClause := [(35,false),(83,true),(4,false),(63,true),(78,false),(68,false)]
theorem der_33780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33780 :=
  CNF.rup_sound cl_33780 [cl_28559,cl_33773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28559 v h) (hints_cons _ _ _ (der_33773 v h) (by intro d hd; cases hd)))
def cl_33781 : CNF.NClause := [(35,false),(73,true),(63,true),(78,false),(68,false),(83,true)]
theorem der_33781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33781 :=
  CNF.rup_sound cl_33781 [cl_28560,cl_33730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28560 v h) (hints_cons _ _ _ (der_33730 v h) (by intro d hd; cases hd)))
def cl_33782 : CNF.NClause := [(35,false),(68,true),(4,false),(63,false),(78,false),(73,true)]
theorem der_33782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33782 :=
  CNF.rup_sound cl_33782 [cl_28561,cl_33755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28561 v h) (hints_cons _ _ _ (der_33755 v h) (by intro d hd; cases hd)))
def cl_33783 : CNF.NClause := [(35,false),(68,true),(87,true),(78,false),(83,true),(4,true)]
theorem der_33783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33783 :=
  CNF.rup_sound cl_33783 [cl_28564,cl_28562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28564 v h) (hints_cons _ _ _ (der_28562 v h) (by intro d hd; cases hd)))
def cl_33784 : CNF.NClause := [(35,false),(78,true),(63,false),(73,false),(68,false),(4,true)]
theorem der_33784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33784 :=
  CNF.rup_sound cl_33784 [cl_28566,cl_33734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28566 v h) (hints_cons _ _ _ (der_33734 v h) (by intro d hd; cases hd)))
def cl_33785 : CNF.NClause := [(35,false),(78,true),(4,false),(63,true),(73,false),(68,false)]
theorem der_33785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33785 :=
  CNF.rup_sound cl_33785 [cl_28567,cl_33759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28567 v h) (hints_cons _ _ _ (der_33759 v h) (by intro d hd; cases hd)))
def cl_33786 : CNF.NClause := [(35,false),(83,true),(78,true),(63,true),(73,false),(68,false)]
theorem der_33786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33786 :=
  CNF.rup_sound cl_33786 [cl_28568,cl_33785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28568 v h) (hints_cons _ _ _ (der_33785 v h) (by intro d hd; cases hd)))
def cl_33787 : CNF.NClause := [(35,false),(4,false),(63,false),(73,false),(83,true),(87,true)]
theorem der_33787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33787 :=
  CNF.rup_sound cl_33787 [cl_28569,cl_28565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28569 v h) (hints_cons _ _ _ (der_28565 v h) (by intro d hd; cases hd)))
def cl_33788 : CNF.NClause := [(35,false),(68,true),(87,true),(63,false),(73,false),(83,true)]
theorem der_33788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33788 :=
  CNF.rup_sound cl_33788 [cl_28570,cl_33787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28570 v h) (hints_cons _ _ _ (der_33787 v h) (by intro d hd; cases hd)))
def cl_33789 : CNF.NClause := [(35,false),(78,true),(4,false),(63,true),(73,false),(87,true)]
theorem der_33789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33789 :=
  CNF.rup_sound cl_33789 [cl_28571,cl_33785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28571 v h) (hints_cons _ _ _ (der_33785 v h) (by intro d hd; cases hd)))
def cl_33790 : CNF.NClause := [(35,false),(73,false),(78,true),(68,true),(63,true),(87,true)]
theorem der_33790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33790 :=
  CNF.rup_sound cl_33790 [cl_28572,cl_33789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28572 v h) (hints_cons _ _ _ (der_33789 v h) (by intro d hd; cases hd)))
def cl_33791 : CNF.NClause := [(35,false),(73,true),(78,true),(4,false),(63,false),(68,false)]
theorem der_33791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33791 :=
  CNF.rup_sound cl_33791 [cl_28573,cl_33741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28573 v h) (hints_cons _ _ _ (der_33741 v h) (by intro d hd; cases hd)))
def cl_33792 : CNF.NClause := [(35,false),(68,false),(73,true),(78,true),(63,false),(83,true)]
theorem der_33792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33792 :=
  CNF.rup_sound cl_33792 [cl_28574,cl_33791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28574 v h) (hints_cons _ _ _ (der_33791 v h) (by intro d hd; cases hd)))
def cl_33793 : CNF.NClause := [(35,false),(78,true),(4,false),(63,true),(68,false),(83,true)]
theorem der_33793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33793 :=
  CNF.rup_sound cl_33793 [cl_28575,cl_33785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28575 v h) (hints_cons _ _ _ (der_33785 v h) (by intro d hd; cases hd)))
def cl_33794 : CNF.NClause := [(35,false),(83,true),(78,true),(63,true),(68,false),(87,true)]
theorem der_33794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33794 :=
  CNF.rup_sound cl_33794 [cl_28576,cl_33793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28576 v h) (hints_cons _ _ _ (der_33793 v h) (by intro d hd; cases hd)))
def cl_33795 : CNF.NClause := [(35,false),(73,true),(78,true),(68,true),(4,false),(63,false)]
theorem der_33795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33795 :=
  CNF.rup_sound cl_33795 [cl_28577,cl_33768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28577 v h) (hints_cons _ _ _ (der_33768 v h) (by intro d hd; cases hd)))
def cl_33796 : CNF.NClause := [(35,false),(73,true),(78,true),(68,true),(4,true),(63,false)]
theorem der_33796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33796 :=
  CNF.rup_sound cl_33796 [cl_28578,cl_33769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28578 v h) (hints_cons _ _ _ (der_33769 v h) (by intro d hd; cases hd)))
def cl_33797 : CNF.NClause := [(35,false),(83,true),(73,true),(68,true),(4,true),(87,true)]
theorem der_33797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33797 :=
  CNF.rup_sound cl_33797 [cl_28580,cl_33783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28580 v h) (hints_cons _ _ _ (der_33783 v h) (by intro d hd; cases hd)))
def cl_33802 : CNF.NClause := [(57,false),(91,false),(62,true),(79,false),(75,false),(83,false)]
theorem der_33802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33802 :=
  CNF.rup_sound cl_33802 [cl_28585,cl_28584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28585 v h) (hints_cons _ _ _ (der_28584 v h) (by intro d hd; cases hd)))
def cl_33803 : CNF.NClause := [(57,false),(91,false),(62,true),(79,false),(71,false),(83,false)]
theorem der_33803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33803 :=
  CNF.rup_sound cl_33803 [cl_28587,cl_32374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28587 v h) (hints_cons _ _ _ (der_32374 v h) (by intro d hd; cases hd)))
def cl_33804 : CNF.NClause := [(57,false),(83,false),(71,true),(91,false),(62,false),(79,false)]
theorem der_33804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33804 :=
  CNF.rup_sound cl_33804 [cl_28589,cl_28588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28589 v h) (hints_cons _ _ _ (der_28588 v h) (by intro d hd; cases hd)))
def cl_33806 : CNF.NClause := [(57,false),(71,true),(62,true),(91,false),(79,false),(83,false)]
theorem der_33806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33806 :=
  CNF.rup_sound cl_33806 [cl_28591,cl_33802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28591 v h) (hints_cons _ _ _ (der_33802 v h) (by intro d hd; cases hd)))
def cl_33807 : CNF.NClause := [(57,false),(75,false),(62,true),(91,false),(71,false),(83,false)]
theorem der_33807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33807 :=
  CNF.rup_sound cl_33807 [cl_28593,cl_32375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28593 v h) (hints_cons _ _ _ (der_32375 v h) (by intro d hd; cases hd)))
def cl_33808 : CNF.NClause := [(57,false),(75,false),(71,true),(91,false),(62,false),(83,false)]
theorem der_33808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33808 :=
  CNF.rup_sound cl_33808 [cl_28595,cl_28594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28595 v h) (hints_cons _ _ _ (der_28594 v h) (by intro d hd; cases hd)))
def cl_33810 : CNF.NClause := [(57,false),(71,false),(75,true),(91,false),(26,true),(83,false)]
theorem der_33810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33810 :=
  CNF.rup_sound cl_33810 [cl_28599,cl_32370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28599 v h) (hints_cons _ _ _ (der_32370 v h) (by intro d hd; cases hd)))
def cl_33811 : CNF.NClause := [(57,false),(71,false),(62,true),(91,false),(26,false),(83,false)]
theorem der_33811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33811 :=
  CNF.rup_sound cl_33811 [cl_28600,cl_33807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28600 v h) (hints_cons _ _ _ (der_33807 v h) (by intro d hd; cases hd)))
def cl_33816 : CNF.NClause := [(57,false),(75,false),(62,true),(91,false),(79,false),(71,false)]
theorem der_33816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33816 :=
  CNF.rup_sound cl_33816 [cl_28606,cl_26733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28606 v h) (hints_cons _ _ _ (der_26733 v h) (by intro d hd; cases hd)))
def cl_33817 : CNF.NClause := [(57,false),(75,false),(71,true),(91,false),(62,false),(79,false)]
theorem der_33817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33817 :=
  CNF.rup_sound cl_33817 [cl_28608,cl_28607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28608 v h) (hints_cons _ _ _ (der_28607 v h) (by intro d hd; cases hd)))
def cl_33818 : CNF.NClause := [(57,false),(75,false),(26,false),(91,false),(79,false),(71,true)]
theorem der_33818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33818 :=
  CNF.rup_sound cl_33818 [cl_28609,cl_33817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28609 v h) (hints_cons _ _ _ (der_33817 v h) (by intro d hd; cases hd)))
def cl_33820 : CNF.NClause := [(57,false),(71,false),(75,true),(91,false),(79,false),(26,true)]
theorem der_33820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33820 :=
  CNF.rup_sound cl_33820 [cl_28612,cl_32371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28612 v h) (hints_cons _ _ _ (der_32371 v h) (by intro d hd; cases hd)))
def cl_33821 : CNF.NClause := [(57,false),(71,false),(62,true),(75,true),(91,false),(79,false)]
theorem der_33821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33821 :=
  CNF.rup_sound cl_33821 [cl_28613,cl_32371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28613 v h) (hints_cons _ _ _ (der_32371 v h) (by intro d hd; cases hd)))
def cl_33822 : CNF.NClause := [(57,false),(71,true),(26,false),(91,false),(62,false),(79,false)]
theorem der_33822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33822 :=
  CNF.rup_sound cl_33822 [cl_28614,cl_33817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28614 v h) (hints_cons _ _ _ (der_33817 v h) (by intro d hd; cases hd)))
def cl_33823 : CNF.NClause := [(57,false),(75,true),(91,false),(62,false),(79,false),(71,true)]
theorem der_33823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33823 :=
  CNF.rup_sound cl_33823 [cl_28615,cl_33804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28615 v h) (hints_cons _ _ _ (der_33804 v h) (by intro d hd; cases hd)))
def cl_33824 : CNF.NClause := [(57,false),(26,false),(62,true),(71,true),(91,false),(79,false)]
theorem der_33824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33824 :=
  CNF.rup_sound cl_33824 [cl_28616,cl_33818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28616 v h) (hints_cons _ _ _ (der_33818 v h) (by intro d hd; cases hd)))
def cl_33825 : CNF.NClause := [(57,false),(75,true),(62,true),(26,true),(91,false),(79,false)]
theorem der_33825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33825 :=
  CNF.rup_sound cl_33825 [cl_28617,cl_32371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28617 v h) (hints_cons _ _ _ (der_32371 v h) (by intro d hd; cases hd)))
def cl_33826 : CNF.NClause := [(57,false),(75,false),(79,true),(91,false),(71,false),(26,true)]
theorem der_33826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33826 :=
  CNF.rup_sound cl_33826 [cl_28619,cl_32379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28619 v h) (hints_cons _ _ _ (der_32379 v h) (by intro d hd; cases hd)))
def cl_33827 : CNF.NClause := [(57,false),(71,false),(62,true),(91,false),(26,false),(75,false)]
theorem der_33827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33827 :=
  CNF.rup_sound cl_33827 [cl_28620,cl_33816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28620 v h) (hints_cons _ _ _ (der_33816 v h) (by intro d hd; cases hd)))
def cl_33829 : CNF.NClause := [(57,false),(79,true),(91,false),(62,false),(75,false),(71,true)]
theorem der_33829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33829 :=
  CNF.rup_sound cl_33829 [cl_28622,cl_33808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28622 v h) (hints_cons _ _ _ (der_33808 v h) (by intro d hd; cases hd)))
def cl_33830 : CNF.NClause := [(57,false),(71,true),(26,false),(79,true),(91,false),(75,false)]
theorem der_33830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33830 :=
  CNF.rup_sound cl_33830 [cl_28623,cl_33829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28623 v h) (hints_cons _ _ _ (der_33829 v h) (by intro d hd; cases hd)))
def cl_33831 : CNF.NClause := [(57,false),(75,false),(71,true),(79,true),(26,true),(91,false)]
theorem der_33831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33831 :=
  CNF.rup_sound cl_33831 [cl_28624,cl_33829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28624 v h) (hints_cons _ _ _ (der_33829 v h) (by intro d hd; cases hd)))
def cl_33833 : CNF.NClause := [(57,false),(71,false),(75,true),(79,true),(91,false),(26,true)]
theorem der_33833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33833 :=
  CNF.rup_sound cl_33833 [cl_28626,cl_32373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28626 v h) (hints_cons _ _ _ (der_32373 v h) (by intro d hd; cases hd)))
def cl_33834 : CNF.NClause := [(57,false),(71,false),(62,true),(75,true),(79,true),(91,false)]
theorem der_33834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33834 :=
  CNF.rup_sound cl_33834 [cl_28627,cl_32373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28627 v h) (hints_cons _ _ _ (der_32373 v h) (by intro d hd; cases hd)))
def cl_33835 : CNF.NClause := [(57,false),(71,true),(26,false),(79,true),(91,false),(62,false)]
theorem der_33835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33835 :=
  CNF.rup_sound cl_33835 [cl_28628,cl_33829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28628 v h) (hints_cons _ _ _ (der_33829 v h) (by intro d hd; cases hd)))
def cl_33836 : CNF.NClause := [(57,false),(62,false),(71,true),(79,true),(26,true),(91,false)]
theorem der_33836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33836 :=
  CNF.rup_sound cl_33836 [cl_28629,cl_33829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28629 v h) (hints_cons _ _ _ (der_33829 v h) (by intro d hd; cases hd)))
def cl_33838 : CNF.NClause := [(57,false),(62,true),(75,true),(79,true),(91,false),(83,true)]
theorem der_33838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33838 :=
  CNF.rup_sound cl_33838 [cl_28631,cl_33834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28631 v h) (hints_cons _ _ _ (der_33834 v h) (by intro d hd; cases hd)))
def cl_33839 : CNF.NClause := [(57,false),(79,false),(26,true),(71,false),(75,false),(83,false)]
theorem der_33839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33839 :=
  CNF.rup_sound cl_33839 [cl_28632,cl_28581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28632 v h) (hints_cons _ _ _ (der_28581 v h) (by intro d hd; cases hd)))
def cl_33840 : CNF.NClause := [(57,false),(75,false),(62,true),(79,false),(71,false),(83,false)]
theorem der_33840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33840 :=
  CNF.rup_sound cl_33840 [cl_28633,cl_26737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28633 v h) (hints_cons _ _ _ (der_26737 v h) (by intro d hd; cases hd)))
def cl_33841 : CNF.NClause := [(57,false),(62,false),(71,true),(79,false),(75,false),(83,false)]
theorem der_33841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33841 :=
  CNF.rup_sound cl_33841 [cl_28635,cl_28634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28635 v h) (hints_cons _ _ _ (der_28634 v h) (by intro d hd; cases hd)))
def cl_33842 : CNF.NClause := [(57,false),(71,true),(26,false),(79,false),(75,false),(83,false)]
theorem der_33842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33842 :=
  CNF.rup_sound cl_33842 [cl_28636,cl_33841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28636 v h) (hints_cons _ _ _ (der_33841 v h) (by intro d hd; cases hd)))
def cl_33843 : CNF.NClause := [(57,false),(83,false),(62,true),(79,false),(75,false),(26,true)]
theorem der_33843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33843 :=
  CNF.rup_sound cl_33843 [cl_28637,cl_33802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28637 v h) (hints_cons _ _ _ (der_33802 v h) (by intro d hd; cases hd)))
def cl_33844 : CNF.NClause := [(57,false),(83,false),(75,true),(79,false),(71,false),(26,true)]
theorem der_33844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33844 :=
  CNF.rup_sound cl_33844 [cl_28639,cl_32374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28639 v h) (hints_cons _ _ _ (der_32374 v h) (by intro d hd; cases hd)))
def cl_33845 : CNF.NClause := [(57,false),(83,false),(62,true),(75,true),(79,false),(71,false)]
theorem der_33845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33845 :=
  CNF.rup_sound cl_33845 [cl_28640,cl_32374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28640 v h) (hints_cons _ _ _ (der_32374 v h) (by intro d hd; cases hd)))
def cl_33847 : CNF.NClause := [(57,false),(71,true),(75,true),(62,false),(79,false),(83,false)]
theorem der_33847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33847 :=
  CNF.rup_sound cl_33847 [cl_28642,cl_33804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28642 v h) (hints_cons _ _ _ (der_33804 v h) (by intro d hd; cases hd)))
def cl_33848 : CNF.NClause := [(57,false),(75,true),(26,false),(71,true),(79,false),(83,false)]
theorem der_33848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33848 :=
  CNF.rup_sound cl_33848 [cl_28643,cl_33847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28643 v h) (hints_cons _ _ _ (der_33847 v h) (by intro d hd; cases hd)))
def cl_33849 : CNF.NClause := [(57,false),(75,true),(71,true),(26,true),(79,false),(83,false)]
theorem der_33849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33849 :=
  CNF.rup_sound cl_33849 [cl_28644,cl_33847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28644 v h) (hints_cons _ _ _ (der_33847 v h) (by intro d hd; cases hd)))
def cl_33850 : CNF.NClause := [(57,false),(75,false),(79,true),(71,false),(26,true),(83,false)]
theorem der_33850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33850 :=
  CNF.rup_sound cl_33850 [cl_28646,cl_32375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28646 v h) (hints_cons _ _ _ (der_32375 v h) (by intro d hd; cases hd)))
def cl_33851 : CNF.NClause := [(57,false),(83,false),(62,true),(71,false),(75,false),(26,false)]
theorem der_33851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33851 :=
  CNF.rup_sound cl_33851 [cl_28647,cl_33807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28647 v h) (hints_cons _ _ _ (der_33807 v h) (by intro d hd; cases hd)))
def cl_33852 : CNF.NClause := [(57,false),(75,false),(26,false),(62,false),(71,true),(83,false)]
theorem der_33852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33852 :=
  CNF.rup_sound cl_33852 [cl_28648,cl_33841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28648 v h) (hints_cons _ _ _ (der_33841 v h) (by intro d hd; cases hd)))
def cl_33853 : CNF.NClause := [(57,false),(83,false),(79,true),(62,false),(75,false),(71,true)]
theorem der_33853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33853 :=
  CNF.rup_sound cl_33853 [cl_28649,cl_33808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28649 v h) (hints_cons _ _ _ (der_33808 v h) (by intro d hd; cases hd)))
def cl_33854 : CNF.NClause := [(57,false),(75,false),(26,false),(62,true),(71,true),(83,false)]
theorem der_33854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33854 :=
  CNF.rup_sound cl_33854 [cl_28650,cl_33842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28650 v h) (hints_cons _ _ _ (der_33842 v h) (by intro d hd; cases hd)))
def cl_33855 : CNF.NClause := [(57,false),(75,false),(71,true),(62,true),(79,true),(83,false)]
theorem der_33855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33855 :=
  CNF.rup_sound cl_33855 [cl_28651,cl_33854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28651 v h) (hints_cons _ _ _ (der_33854 v h) (by intro d hd; cases hd)))
def cl_33856 : CNF.NClause := [(57,false),(71,false),(79,true),(62,false),(26,false),(83,false)]
theorem der_33856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33856 :=
  CNF.rup_sound cl_33856 [cl_28652,cl_28645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28652 v h) (hints_cons _ _ _ (der_28645 v h) (by intro d hd; cases hd)))
def cl_33857 : CNF.NClause := [(57,false),(71,false),(75,true),(79,true),(26,true),(83,false)]
theorem der_33857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33857 :=
  CNF.rup_sound cl_33857 [cl_28653,cl_32376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28653 v h) (hints_cons _ _ _ (der_32376 v h) (by intro d hd; cases hd)))
def cl_33858 : CNF.NClause := [(57,false),(71,false),(62,true),(75,true),(79,true),(83,false)]
theorem der_33858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33858 :=
  CNF.rup_sound cl_33858 [cl_28654,cl_32376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28654 v h) (hints_cons _ _ _ (der_32376 v h) (by intro d hd; cases hd)))
def cl_33859 : CNF.NClause := [(57,false),(62,false),(26,false),(75,true),(71,true),(83,false)]
theorem der_33859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33859 :=
  CNF.rup_sound cl_33859 [cl_28655,cl_33847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28655 v h) (hints_cons _ _ _ (der_33847 v h) (by intro d hd; cases hd)))
def cl_33860 : CNF.NClause := [(57,false),(83,false),(71,true),(75,true),(26,true),(62,false)]
theorem der_33860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33860 :=
  CNF.rup_sound cl_33860 [cl_28656,cl_33847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28656 v h) (hints_cons _ _ _ (der_33847 v h) (by intro d hd; cases hd)))
def cl_33862 : CNF.NClause := [(57,false),(75,true),(62,true),(26,true),(79,true),(83,false)]
theorem der_33862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33862 :=
  CNF.rup_sound cl_33862 [cl_28658,cl_32376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28658 v h) (hints_cons _ _ _ (der_32376 v h) (by intro d hd; cases hd)))
def cl_33863 : CNF.NClause := [(57,false),(83,true),(79,false),(71,false),(75,false),(26,true)]
theorem der_33863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33863 :=
  CNF.rup_sound cl_33863 [cl_28660,cl_32377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28660 v h) (hints_cons _ _ _ (der_32377 v h) (by intro d hd; cases hd)))
def cl_33864 : CNF.NClause := [(57,false),(91,true),(62,true),(79,false),(71,false),(75,false)]
theorem der_33864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33864 :=
  CNF.rup_sound cl_33864 [cl_28661,cl_32377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28661 v h) (hints_cons _ _ _ (der_32377 v h) (by intro d hd; cases hd)))
def cl_33865 : CNF.NClause := [(57,false),(26,false),(62,false),(79,false),(75,false),(71,true)]
theorem der_33865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33865 :=
  CNF.rup_sound cl_33865 [cl_28662,cl_33841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28662 v h) (hints_cons _ _ _ (der_33841 v h) (by intro d hd; cases hd)))
def cl_33866 : CNF.NClause := [(57,false),(71,true),(62,false),(79,false),(75,false),(26,true)]
theorem der_33866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33866 :=
  CNF.rup_sound cl_33866 [cl_28663,cl_33841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28663 v h) (hints_cons _ _ _ (der_33841 v h) (by intro d hd; cases hd)))
def cl_33867 : CNF.NClause := [(57,false),(26,false),(62,true),(79,false),(75,false),(71,true)]
theorem der_33867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33867 :=
  CNF.rup_sound cl_33867 [cl_28664,cl_33854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28664 v h) (hints_cons _ _ _ (der_33854 v h) (by intro d hd; cases hd)))
def cl_33868 : CNF.NClause := [(57,false),(83,true),(71,true),(62,true),(79,false),(75,false)]
theorem der_33868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33868 :=
  CNF.rup_sound cl_33868 [cl_28665,cl_33867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28665 v h) (hints_cons _ _ _ (der_33867 v h) (by intro d hd; cases hd)))
def cl_33870 : CNF.NClause := [(57,false),(83,true),(75,true),(79,false),(71,false),(26,true)]
theorem der_33870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33870 :=
  CNF.rup_sound cl_33870 [cl_28667,cl_32378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28667 v h) (hints_cons _ _ _ (der_32378 v h) (by intro d hd; cases hd)))
def cl_33871 : CNF.NClause := [(57,false),(91,true),(62,true),(79,false),(71,false),(26,false)]
theorem der_33871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33871 :=
  CNF.rup_sound cl_33871 [cl_28668,cl_33864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28668 v h) (hints_cons _ _ _ (der_33864 v h) (by intro d hd; cases hd)))
def cl_33874 : CNF.NClause := [(57,false),(71,true),(62,true),(26,true),(79,false),(83,true)]
theorem der_33874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33874 :=
  CNF.rup_sound cl_33874 [cl_28672,cl_33868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28672 v h) (hints_cons _ _ _ (der_33868 v h) (by intro d hd; cases hd)))
def cl_33875 : CNF.NClause := [(57,false),(83,true),(62,false),(71,false),(75,false),(26,false)]
theorem der_33875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33875 :=
  CNF.rup_sound cl_33875 [cl_28673,cl_28659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28673 v h) (hints_cons _ _ _ (der_28659 v h) (by intro d hd; cases hd)))
def cl_33876 : CNF.NClause := [(57,false),(83,true),(79,true),(62,false),(71,false),(75,false)]
theorem der_33876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33876 :=
  CNF.rup_sound cl_33876 [cl_28674,cl_33875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28674 v h) (hints_cons _ _ _ (der_33875 v h) (by intro d hd; cases hd)))
def cl_33877 : CNF.NClause := [(57,false),(75,false),(62,true),(79,true),(71,false),(91,true)]
theorem der_33877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33877 :=
  CNF.rup_sound cl_33877 [cl_28675,cl_32379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28675 v h) (hints_cons _ _ _ (der_32379 v h) (by intro d hd; cases hd)))
def cl_33878 : CNF.NClause := [(57,false),(83,true),(26,false),(62,false),(75,false),(71,true)]
theorem der_33878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33878 :=
  CNF.rup_sound cl_33878 [cl_28676,cl_33865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28676 v h) (hints_cons _ _ _ (der_33865 v h) (by intro d hd; cases hd)))
def cl_33879 : CNF.NClause := [(57,false),(71,true),(91,true),(62,false),(75,false),(83,true)]
theorem der_33879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33879 :=
  CNF.rup_sound cl_33879 [cl_28677,cl_33878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28677 v h) (hints_cons _ _ _ (der_33878 v h) (by intro d hd; cases hd)))
def cl_33882 : CNF.NClause := [(57,false),(71,false),(75,true),(79,true),(62,false),(26,false)]
theorem der_33882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33882 :=
  CNF.rup_sound cl_33882 [cl_28680,cl_33856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28680 v h) (hints_cons _ _ _ (der_33856 v h) (by intro d hd; cases hd)))
def cl_33883 : CNF.NClause := [(57,false),(71,false),(62,true),(75,true),(79,true),(91,true)]
theorem der_33883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33883 :=
  CNF.rup_sound cl_33883 [cl_28682,cl_32380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28682 v h) (hints_cons _ _ _ (der_32380 v h) (by intro d hd; cases hd)))
def cl_33885 : CNF.NClause := [(57,false),(71,true),(75,true),(62,false),(26,true),(91,true)]
theorem der_33885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33885 :=
  CNF.rup_sound cl_33885 [cl_28684,cl_33860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28684 v h) (hints_cons _ _ _ (der_33860 v h) (by intro d hd; cases hd)))
def cl_33887 : CNF.NClause := [(57,false),(75,true),(71,true),(26,true),(83,true),(91,true)]
theorem der_33887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33887 :=
  CNF.rup_sound cl_33887 [cl_28686,cl_33885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28686 v h) (hints_cons _ _ _ (der_33885 v h) (by intro d hd; cases hd)))
def cl_33888 : CNF.NClause := [(51,false),(71,false),(92,false),(69,false),(67,true),(70,false)]
theorem der_33888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33888 :=
  CNF.rup_sound cl_33888 [cl_28690,cl_28689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28690 v h) (hints_cons _ _ _ (der_28689 v h) (by intro d hd; cases hd)))
def cl_33889 : CNF.NClause := [(51,false),(70,false),(92,false),(71,false),(67,true),(68,false)]
theorem der_33889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33889 :=
  CNF.rup_sound cl_33889 [cl_28693,cl_28692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28693 v h) (hints_cons _ _ _ (der_28692 v h) (by intro d hd; cases hd)))
def cl_33890 : CNF.NClause := [(51,false),(67,false),(68,true),(92,false),(71,false),(70,false)]
theorem der_33890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33890 :=
  CNF.rup_sound cl_33890 [cl_28695,cl_28694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28695 v h) (hints_cons _ _ _ (der_28694 v h) (by intro d hd; cases hd)))
def cl_33891 : CNF.NClause := [(51,false),(68,true),(92,false),(71,false),(67,true),(70,false)]
theorem der_33891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33891 :=
  CNF.rup_sound cl_33891 [cl_28697,cl_33888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28697 v h) (hints_cons _ _ _ (der_33888 v h) (by intro d hd; cases hd)))
def cl_33892 : CNF.NClause := [(51,false),(92,false),(68,false),(71,false),(69,false),(67,true)]
theorem der_33892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33892 :=
  CNF.rup_sound cl_33892 [cl_28700,cl_28699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28700 v h) (hints_cons _ _ _ (der_28699 v h) (by intro d hd; cases hd)))
def cl_33893 : CNF.NClause := [(51,false),(71,false),(68,true),(92,false),(67,false),(69,false)]
theorem der_33893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33893 :=
  CNF.rup_sound cl_33893 [cl_28702,cl_28701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28702 v h) (hints_cons _ _ _ (der_28701 v h) (by intro d hd; cases hd)))
def cl_33894 : CNF.NClause := [(51,false),(92,false),(68,true),(71,false),(69,false),(67,true)]
theorem der_33894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33894 :=
  CNF.rup_sound cl_33894 [cl_28704,cl_33888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28704 v h) (hints_cons _ _ _ (der_33888 v h) (by intro d hd; cases hd)))
def cl_33895 : CNF.NClause := [(51,false),(71,false),(69,true),(92,false),(67,false),(68,false)]
theorem der_33895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33895 :=
  CNF.rup_sound cl_33895 [cl_28706,cl_28705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28706 v h) (hints_cons _ _ _ (der_28705 v h) (by intro d hd; cases hd)))
def cl_33897 : CNF.NClause := [(51,false),(71,false),(69,true),(92,false),(67,true),(68,false)]
theorem der_33897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33897 :=
  CNF.rup_sound cl_33897 [cl_28708,cl_33889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28708 v h) (hints_cons _ _ _ (der_33889 v h) (by intro d hd; cases hd)))
def cl_33899 : CNF.NClause := [(51,false),(67,false),(68,true),(69,true),(92,false),(71,false)]
theorem der_33899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33899 :=
  CNF.rup_sound cl_33899 [cl_28710,cl_33890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28710 v h) (hints_cons _ _ _ (der_33890 v h) (by intro d hd; cases hd)))
def cl_33901 : CNF.NClause := [(51,false),(68,true),(20,true),(92,false),(71,false),(67,true)]
theorem der_33901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33901 :=
  CNF.rup_sound cl_33901 [cl_28712,cl_33894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28712 v h) (hints_cons _ _ _ (der_33894 v h) (by intro d hd; cases hd)))
def cl_33902 : CNF.NClause := [(51,false),(69,false),(92,false),(67,true),(70,false),(68,false)]
theorem der_33902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33902 :=
  CNF.rup_sound cl_33902 [cl_28715,cl_28714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28715 v h) (hints_cons _ _ _ (der_28714 v h) (by intro d hd; cases hd)))
def cl_33903 : CNF.NClause := [(51,false),(69,false),(68,true),(92,false),(67,false),(70,false)]
theorem der_33903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33903 :=
  CNF.rup_sound cl_33903 [cl_28717,cl_28716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28717 v h) (hints_cons _ _ _ (der_28716 v h) (by intro d hd; cases hd)))
def cl_33904 : CNF.NClause := [(51,false),(68,true),(92,false),(69,false),(67,true),(70,false)]
theorem der_33904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33904 :=
  CNF.rup_sound cl_33904 [cl_28719,cl_33888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28719 v h) (hints_cons _ _ _ (der_33888 v h) (by intro d hd; cases hd)))
def cl_33905 : CNF.NClause := [(51,false),(70,false),(69,true),(92,false),(67,false),(68,false)]
theorem der_33905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33905 :=
  CNF.rup_sound cl_33905 [cl_28721,cl_28720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28721 v h) (hints_cons _ _ _ (der_28720 v h) (by intro d hd; cases hd)))
def cl_33906 : CNF.NClause := [(51,false),(69,true),(20,false),(92,false),(70,false),(68,false)]
theorem der_33906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33906 :=
  CNF.rup_sound cl_33906 [cl_28722,cl_33905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28722 v h) (hints_cons _ _ _ (der_33905 v h) (by intro d hd; cases hd)))
def cl_33907 : CNF.NClause := [(51,false),(69,true),(92,false),(67,true),(70,false),(68,false)]
theorem der_33907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33907 :=
  CNF.rup_sound cl_33907 [cl_28723,cl_33889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28723 v h) (hints_cons _ _ _ (der_33889 v h) (by intro d hd; cases hd)))
def cl_33908 : CNF.NClause := [(51,false),(69,true),(20,false),(92,false),(67,false),(70,false)]
theorem der_33908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33908 :=
  CNF.rup_sound cl_33908 [cl_28724,cl_33905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28724 v h) (hints_cons _ _ _ (der_33905 v h) (by intro d hd; cases hd)))
def cl_33909 : CNF.NClause := [(51,false),(70,false),(68,true),(69,true),(92,false),(67,false)]
theorem der_33909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33909 :=
  CNF.rup_sound cl_33909 [cl_28725,cl_33890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28725 v h) (hints_cons _ _ _ (der_33890 v h) (by intro d hd; cases hd)))
def cl_33910 : CNF.NClause := [(51,false),(69,true),(20,false),(92,false),(67,true),(70,false)]
theorem der_33910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33910 :=
  CNF.rup_sound cl_33910 [cl_28726,cl_33906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28726 v h) (hints_cons _ _ _ (der_33906 v h) (by intro d hd; cases hd)))
def cl_33911 : CNF.NClause := [(51,false),(69,true),(68,true),(92,false),(67,true),(70,false)]
theorem der_33911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33911 :=
  CNF.rup_sound cl_33911 [cl_28727,cl_33910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28727 v h) (hints_cons _ _ _ (der_33910 v h) (by intro d hd; cases hd)))
def cl_33912 : CNF.NClause := [(51,false),(92,false),(70,true),(67,false),(69,false),(68,false)]
theorem der_33912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33912 :=
  CNF.rup_sound cl_33912 [cl_28729,cl_28728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28729 v h) (hints_cons _ _ _ (der_28728 v h) (by intro d hd; cases hd)))
def cl_33913 : CNF.NClause := [(51,false),(67,true),(20,false),(92,false),(69,false),(68,false)]
theorem der_33913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33913 :=
  CNF.rup_sound cl_33913 [cl_28730,cl_33902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28730 v h) (hints_cons _ _ _ (der_33902 v h) (by intro d hd; cases hd)))
def cl_33914 : CNF.NClause := [(51,false),(70,true),(68,false),(92,false),(69,false),(20,true)]
theorem der_33914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33914 :=
  CNF.rup_sound cl_33914 [cl_28731,cl_33912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28731 v h) (hints_cons _ _ _ (der_33912 v h) (by intro d hd; cases hd)))
def cl_33916 : CNF.NClause := [(51,false),(68,true),(70,true),(92,false),(67,false),(69,false)]
theorem der_33916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33916 :=
  CNF.rup_sound cl_33916 [cl_28733,cl_33893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28733 v h) (hints_cons _ _ _ (der_33893 v h) (by intro d hd; cases hd)))
def cl_33917 : CNF.NClause := [(51,false),(92,false),(70,true),(20,false),(69,false),(67,true)]
theorem der_33917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33917 :=
  CNF.rup_sound cl_33917 [cl_28734,cl_33913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28734 v h) (hints_cons _ _ _ (der_33913 v h) (by intro d hd; cases hd)))
def cl_33918 : CNF.NClause := [(51,false),(70,true),(20,true),(92,false),(69,false),(67,true)]
theorem der_33918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33918 :=
  CNF.rup_sound cl_33918 [cl_28735,cl_33914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28735 v h) (hints_cons _ _ _ (der_33914 v h) (by intro d hd; cases hd)))
def cl_33919 : CNF.NClause := [(51,false),(67,false),(69,true),(20,false),(92,false),(68,false)]
theorem der_33919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33919 :=
  CNF.rup_sound cl_33919 [cl_28736,cl_33905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28736 v h) (hints_cons _ _ _ (der_33905 v h) (by intro d hd; cases hd)))
def cl_33920 : CNF.NClause := [(51,false),(67,false),(69,true),(92,false),(20,true),(68,false)]
theorem der_33920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33920 :=
  CNF.rup_sound cl_33920 [cl_28737,cl_33905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28737 v h) (hints_cons _ _ _ (der_33905 v h) (by intro d hd; cases hd)))
def cl_33921 : CNF.NClause := [(51,false),(92,false),(69,true),(20,false),(70,true),(68,false)]
theorem der_33921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33921 :=
  CNF.rup_sound cl_33921 [cl_28738,cl_33919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28738 v h) (hints_cons _ _ _ (der_33919 v h) (by intro d hd; cases hd)))
def cl_33922 : CNF.NClause := [(51,false),(67,true),(69,true),(20,true),(92,false),(68,false)]
theorem der_33922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33922 :=
  CNF.rup_sound cl_33922 [cl_28739,cl_33907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28739 v h) (hints_cons _ _ _ (der_33907 v h) (by intro d hd; cases hd)))
def cl_33924 : CNF.NClause := [(51,false),(67,false),(68,true),(69,true),(20,true),(92,false)]
theorem der_33924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33924 :=
  CNF.rup_sound cl_33924 [cl_28741,cl_33909] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28741 v h) (hints_cons _ _ _ (der_33909 v h) (by intro d hd; cases hd)))
def cl_33925 : CNF.NClause := [(51,false),(71,true),(70,true),(69,true),(20,false),(92,false)]
theorem der_33925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33925 :=
  CNF.rup_sound cl_33925 [cl_28742,cl_33921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28742 v h) (hints_cons _ _ _ (der_33921 v h) (by intro d hd; cases hd)))
def cl_33926 : CNF.NClause := [(51,false),(68,true),(71,true),(69,true),(92,false),(67,true)]
theorem der_33926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33926 :=
  CNF.rup_sound cl_33926 [cl_28743,cl_33911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28743 v h) (hints_cons _ _ _ (der_33911 v h) (by intro d hd; cases hd)))
def cl_33927 : CNF.NClause := [(51,false),(70,false),(71,false),(69,false),(67,true),(68,false)]
theorem der_33927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33927 :=
  CNF.rup_sound cl_33927 [cl_28746,cl_28745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28746 v h) (hints_cons _ _ _ (der_28745 v h) (by intro d hd; cases hd)))
def cl_33928 : CNF.NClause := [(51,false),(20,true),(67,false),(71,false),(69,false),(70,false)]
theorem der_33928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33928 :=
  CNF.rup_sound cl_33928 [cl_28748,cl_28744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28748 v h) (hints_cons _ _ _ (der_28744 v h) (by intro d hd; cases hd)))
def cl_33929 : CNF.NClause := [(51,false),(69,false),(71,false),(20,false),(67,true),(70,false)]
theorem der_33929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33929 :=
  CNF.rup_sound cl_33929 [cl_28749,cl_33888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28749 v h) (hints_cons _ _ _ (der_33888 v h) (by intro d hd; cases hd)))
def cl_33930 : CNF.NClause := [(51,false),(71,false),(68,true),(69,false),(67,true),(70,false)]
theorem der_33930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33930 :=
  CNF.rup_sound cl_33930 [cl_28750,cl_33929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28750 v h) (hints_cons _ _ _ (der_33929 v h) (by intro d hd; cases hd)))
def cl_33931 : CNF.NClause := [(51,false),(70,false),(69,true),(67,false),(71,false),(68,false)]
theorem der_33931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33931 :=
  CNF.rup_sound cl_33931 [cl_28752,cl_28751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28752 v h) (hints_cons _ _ _ (der_28751 v h) (by intro d hd; cases hd)))
def cl_33932 : CNF.NClause := [(51,false),(20,false),(71,false),(67,true),(70,false),(68,false)]
theorem der_33932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33932 :=
  CNF.rup_sound cl_33932 [cl_28753,cl_28745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28753 v h) (hints_cons _ _ _ (der_28745 v h) (by intro d hd; cases hd)))
def cl_33933 : CNF.NClause := [(51,false),(69,true),(20,false),(67,false),(71,false),(70,false)]
theorem der_33933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33933 :=
  CNF.rup_sound cl_33933 [cl_28755,cl_28751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28755 v h) (hints_cons _ _ _ (der_28751 v h) (by intro d hd; cases hd)))
def cl_33934 : CNF.NClause := [(51,false),(69,true),(67,false),(71,false),(70,false),(92,true)]
theorem der_33934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33934 :=
  CNF.rup_sound cl_33934 [cl_28756,cl_33933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28756 v h) (hints_cons _ _ _ (der_33933 v h) (by intro d hd; cases hd)))
def cl_33935 : CNF.NClause := [(51,false),(69,true),(20,false),(71,false),(67,true),(70,false)]
theorem der_33935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33935 :=
  CNF.rup_sound cl_33935 [cl_28757,cl_33932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28757 v h) (hints_cons _ _ _ (der_33932 v h) (by intro d hd; cases hd)))
def cl_33936 : CNF.NClause := [(51,false),(69,true),(68,true),(71,false),(67,true),(70,false)]
theorem der_33936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33936 :=
  CNF.rup_sound cl_33936 [cl_28758,cl_33935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28758 v h) (hints_cons _ _ _ (der_33935 v h) (by intro d hd; cases hd)))
def cl_33937 : CNF.NClause := [(51,false),(67,false),(20,true),(71,false),(69,false),(68,false)]
theorem der_33937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33937 :=
  CNF.rup_sound cl_33937 [cl_28760,cl_28744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28760 v h) (hints_cons _ _ _ (der_28744 v h) (by intro d hd; cases hd)))
def cl_33938 : CNF.NClause := [(51,false),(68,false),(71,false),(69,false),(67,true),(20,false)]
theorem der_33938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33938 :=
  CNF.rup_sound cl_33938 [cl_28761,cl_33892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28761 v h) (hints_cons _ _ _ (der_33892 v h) (by intro d hd; cases hd)))
def cl_33939 : CNF.NClause := [(51,false),(71,false),(70,true),(20,true),(69,false),(68,false)]
theorem der_33939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33939 :=
  CNF.rup_sound cl_33939 [cl_28762,cl_33914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28762 v h) (hints_cons _ _ _ (der_33914 v h) (by intro d hd; cases hd)))
def cl_33940 : CNF.NClause := [(51,false),(70,true),(20,false),(67,false),(71,false),(69,false)]
theorem der_33940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33940 :=
  CNF.rup_sound cl_33940 [cl_28763,cl_28759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28763 v h) (hints_cons _ _ _ (der_28759 v h) (by intro d hd; cases hd)))
def cl_33941 : CNF.NClause := [(51,false),(92,true),(70,true),(67,false),(71,false),(69,false)]
theorem der_33941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33941 :=
  CNF.rup_sound cl_33941 [cl_28764,cl_33940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28764 v h) (hints_cons _ _ _ (der_33940 v h) (by intro d hd; cases hd)))
def cl_33942 : CNF.NClause := [(51,false),(71,false),(68,true),(70,true),(20,false),(69,false)]
theorem der_33942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33942 :=
  CNF.rup_sound cl_33942 [cl_28765,cl_33940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28765 v h) (hints_cons _ _ _ (der_33940 v h) (by intro d hd; cases hd)))
def cl_33943 : CNF.NClause := [(51,false),(68,true),(70,true),(71,false),(69,false),(67,true)]
theorem der_33943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33943 :=
  CNF.rup_sound cl_33943 [cl_28766,cl_33942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28766 v h) (hints_cons _ _ _ (der_33942 v h) (by intro d hd; cases hd)))
def cl_33944 : CNF.NClause := [(51,false),(69,true),(67,false),(71,false),(20,true),(68,false)]
theorem der_33944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33944 :=
  CNF.rup_sound cl_33944 [cl_28768,cl_33895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28768 v h) (hints_cons _ _ _ (der_33895 v h) (by intro d hd; cases hd)))
def cl_33945 : CNF.NClause := [(51,false),(71,false),(69,true),(20,false),(67,true),(68,false)]
theorem der_33945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33945 :=
  CNF.rup_sound cl_33945 [cl_28769,cl_33932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28769 v h) (hints_cons _ _ _ (der_33932 v h) (by intro d hd; cases hd)))
def cl_33946 : CNF.NClause := [(51,false),(70,true),(68,false),(69,true),(71,false),(67,true)]
theorem der_33946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33946 :=
  CNF.rup_sound cl_33946 [cl_28770,cl_33945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28770 v h) (hints_cons _ _ _ (der_33945 v h) (by intro d hd; cases hd)))
def cl_33947 : CNF.NClause := [(51,false),(67,false),(68,true),(69,true),(20,false),(71,false)]
theorem der_33947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33947 :=
  CNF.rup_sound cl_33947 [cl_28771,cl_33933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28771 v h) (hints_cons _ _ _ (der_33933 v h) (by intro d hd; cases hd)))
def cl_33948 : CNF.NClause := [(51,false),(71,false),(70,true),(69,true),(20,true),(67,false)]
theorem der_33948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33948 :=
  CNF.rup_sound cl_33948 [cl_28772,cl_33944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28772 v h) (hints_cons _ _ _ (der_33944 v h) (by intro d hd; cases hd)))
def cl_33949 : CNF.NClause := [(51,false),(68,true),(70,true),(20,false),(71,false),(67,true)]
theorem der_33949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33949 :=
  CNF.rup_sound cl_33949 [cl_28773,cl_33943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28773 v h) (hints_cons _ _ _ (der_33943 v h) (by intro d hd; cases hd)))
def cl_33950 : CNF.NClause := [(51,false),(68,true),(70,true),(20,true),(71,false),(67,true)]
theorem der_33950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33950 :=
  CNF.rup_sound cl_33950 [cl_28774,cl_33901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28774 v h) (hints_cons _ _ _ (der_33901 v h) (by intro d hd; cases hd)))
def cl_33951 : CNF.NClause := [(51,false),(70,false),(71,true),(67,false),(69,false),(68,false)]
theorem der_33951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33951 :=
  CNF.rup_sound cl_33951 [cl_28776,cl_28775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28776 v h) (hints_cons _ _ _ (der_28775 v h) (by intro d hd; cases hd)))
def cl_33952 : CNF.NClause := [(51,false),(69,false),(20,false),(67,true),(70,false),(68,false)]
theorem der_33952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33952 :=
  CNF.rup_sound cl_33952 [cl_28777,cl_28714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28777 v h) (hints_cons _ _ _ (der_28714 v h) (by intro d hd; cases hd)))
def cl_33953 : CNF.NClause := [(51,false),(70,false),(71,true),(69,false),(67,true),(68,false)]
theorem der_33953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33953 :=
  CNF.rup_sound cl_33953 [cl_28778,cl_33952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28778 v h) (hints_cons _ _ _ (der_33952 v h) (by intro d hd; cases hd)))
def cl_33955 : CNF.NClause := [(51,false),(92,true),(67,false),(69,false),(70,false),(20,true)]
theorem der_33955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33955 :=
  CNF.rup_sound cl_33955 [cl_28780,cl_33928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28780 v h) (hints_cons _ _ _ (der_33928 v h) (by intro d hd; cases hd)))
def cl_33956 : CNF.NClause := [(51,false),(69,false),(71,true),(20,false),(67,true),(70,false)]
theorem der_33956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33956 :=
  CNF.rup_sound cl_33956 [cl_28781,cl_33952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28781 v h) (hints_cons _ _ _ (der_33952 v h) (by intro d hd; cases hd)))
def cl_33957 : CNF.NClause := [(51,false),(68,true),(71,true),(69,false),(67,true),(70,false)]
theorem der_33957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33957 :=
  CNF.rup_sound cl_33957 [cl_28782,cl_33956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28782 v h) (hints_cons _ _ _ (der_33956 v h) (by intro d hd; cases hd)))
def cl_33958 : CNF.NClause := [(51,false),(69,true),(20,false),(67,false),(70,false),(68,false)]
theorem der_33958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33958 :=
  CNF.rup_sound cl_33958 [cl_28783,cl_28751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28783 v h) (hints_cons _ _ _ (der_28751 v h) (by intro d hd; cases hd)))
def cl_33959 : CNF.NClause := [(51,false),(69,true),(67,false),(70,false),(20,true),(68,false)]
theorem der_33959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33959 :=
  CNF.rup_sound cl_33959 [cl_28784,cl_33905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28784 v h) (hints_cons _ _ _ (der_33905 v h) (by intro d hd; cases hd)))
def cl_33960 : CNF.NClause := [(51,false),(69,true),(20,false),(67,true),(70,false),(68,false)]
theorem der_33960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33960 :=
  CNF.rup_sound cl_33960 [cl_28785,cl_33932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28785 v h) (hints_cons _ _ _ (der_33932 v h) (by intro d hd; cases hd)))
def cl_33961 : CNF.NClause := [(51,false),(70,false),(71,true),(67,true),(20,true),(68,false)]
theorem der_33961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33961 :=
  CNF.rup_sound cl_33961 [cl_28786,cl_33953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28786 v h) (hints_cons _ _ _ (der_33953 v h) (by intro d hd; cases hd)))
def cl_33962 : CNF.NClause := [(51,false),(92,true),(69,true),(20,false),(67,false),(70,false)]
theorem der_33962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33962 :=
  CNF.rup_sound cl_33962 [cl_28787,cl_33933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28787 v h) (hints_cons _ _ _ (der_33933 v h) (by intro d hd; cases hd)))
def cl_33963 : CNF.NClause := [(51,false),(92,true),(71,true),(69,true),(67,false),(70,false)]
theorem der_33963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33963 :=
  CNF.rup_sound cl_33963 [cl_28788,cl_33962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28788 v h) (hints_cons _ _ _ (der_33962 v h) (by intro d hd; cases hd)))
def cl_33964 : CNF.NClause := [(51,false),(71,true),(20,true),(67,true),(70,false),(92,true)]
theorem der_33964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33964 :=
  CNF.rup_sound cl_33964 [cl_28790,cl_33961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28790 v h) (hints_cons _ _ _ (der_33961 v h) (by intro d hd; cases hd)))
def cl_33965 : CNF.NClause := [(51,false),(71,true),(20,false),(67,false),(69,false),(68,false)]
theorem der_33965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33965 :=
  CNF.rup_sound cl_33965 [cl_28791,cl_28775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28791 v h) (hints_cons _ _ _ (der_28775 v h) (by intro d hd; cases hd)))
def cl_33966 : CNF.NClause := [(51,false),(67,false),(20,true),(70,true),(69,false),(68,false)]
theorem der_33966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33966 :=
  CNF.rup_sound cl_33966 [cl_28792,cl_33914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28792 v h) (hints_cons _ _ _ (der_33914 v h) (by intro d hd; cases hd)))
def cl_33967 : CNF.NClause := [(51,false),(20,false),(69,false),(67,true),(68,false),(92,true)]
theorem der_33967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33967 :=
  CNF.rup_sound cl_33967 [cl_28793,cl_33952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28793 v h) (hints_cons _ _ _ (der_33952 v h) (by intro d hd; cases hd)))
def cl_33968 : CNF.NClause := [(51,false),(71,true),(20,true),(69,false),(67,true),(68,false)]
theorem der_33968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33968 :=
  CNF.rup_sound cl_33968 [cl_28794,cl_33953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28794 v h) (hints_cons _ _ _ (der_33953 v h) (by intro d hd; cases hd)))
def cl_33970 : CNF.NClause := [(51,false),(92,true),(70,true),(67,false),(69,false),(20,true)]
theorem der_33970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33970 :=
  CNF.rup_sound cl_33970 [cl_28796,cl_33941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28796 v h) (hints_cons _ _ _ (der_33941 v h) (by intro d hd; cases hd)))
def cl_33972 : CNF.NClause := [(51,false),(68,true),(70,true),(20,true),(69,false),(67,true)]
theorem der_33972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33972 :=
  CNF.rup_sound cl_33972 [cl_28798,cl_33918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28798 v h) (hints_cons _ _ _ (der_33918 v h) (by intro d hd; cases hd)))
def cl_33973 : CNF.NClause := [(51,false),(70,true),(20,false),(67,false),(68,false),(92,true)]
theorem der_33973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33973 :=
  CNF.rup_sound cl_33973 [cl_28799,cl_28767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28799 v h) (hints_cons _ _ _ (der_28767 v h) (by intro d hd; cases hd)))
def cl_33974 : CNF.NClause := [(51,false),(92,true),(70,true),(69,true),(67,false),(68,false)]
theorem der_33974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33974 :=
  CNF.rup_sound cl_33974 [cl_28800,cl_33973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28800 v h) (hints_cons _ _ _ (der_33973 v h) (by intro d hd; cases hd)))
def cl_33976 : CNF.NClause := [(51,false),(92,true),(71,true),(67,true),(20,true),(68,false)]
theorem der_33976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33976 :=
  CNF.rup_sound cl_33976 [cl_28802,cl_33961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28802 v h) (hints_cons _ _ _ (der_33961 v h) (by intro d hd; cases hd)))
def cl_33977 : CNF.NClause := [(51,false),(67,false),(68,true),(69,true),(70,true),(20,false)]
theorem der_33977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33977 :=
  CNF.rup_sound cl_33977 [cl_28803,cl_33947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28803 v h) (hints_cons _ _ _ (der_33947 v h) (by intro d hd; cases hd)))
def cl_33978 : CNF.NClause := [(51,false),(92,true),(71,true),(69,true),(20,true),(67,false)]
theorem der_33978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33978 :=
  CNF.rup_sound cl_33978 [cl_28804,cl_33963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28804 v h) (hints_cons _ _ _ (der_33963 v h) (by intro d hd; cases hd)))
def cl_33979 : CNF.NClause := [(51,false),(69,true),(71,true),(70,true),(20,false),(67,true)]
theorem der_33979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33979 :=
  CNF.rup_sound cl_33979 [cl_28805,cl_33925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28805 v h) (hints_cons _ _ _ (der_33925 v h) (by intro d hd; cases hd)))
def cl_33980 : CNF.NClause := [(51,false),(68,true),(71,true),(70,true),(69,true),(67,true)]
theorem der_33980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33980 :=
  CNF.rup_sound cl_33980 [cl_28806,cl_33926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28806 v h) (hints_cons _ _ _ (der_33926 v h) (by intro d hd; cases hd)))
def cl_33982 : CNF.NClause := [(50,false),(85,false),(71,true),(77,false),(90,false),(74,false)]
theorem der_33982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33982 :=
  CNF.rup_sound cl_33982 [cl_28810,cl_28809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28810 v h) (hints_cons _ _ _ (der_28809 v h) (by intro d hd; cases hd)))
def cl_33983 : CNF.NClause := [(50,false),(71,false),(74,true),(77,false),(85,false),(90,false)]
theorem der_33983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33983 :=
  CNF.rup_sound cl_33983 [cl_28813,cl_28812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28813 v h) (hints_cons _ _ _ (der_28812 v h) (by intro d hd; cases hd)))
def cl_33984 : CNF.NClause := [(50,false),(85,false),(77,false),(19,true),(63,false),(90,false)]
theorem der_33984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33984 :=
  CNF.rup_sound cl_33984 [cl_28815,cl_26749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28815 v h) (hints_cons _ _ _ (der_26749 v h) (by intro d hd; cases hd)))
def cl_33985 : CNF.NClause := [(50,false),(77,false),(19,false),(71,true),(85,false),(90,false)]
theorem der_33985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33985 :=
  CNF.rup_sound cl_33985 [cl_28816,cl_28814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28816 v h) (hints_cons _ _ _ (der_28814 v h) (by intro d hd; cases hd)))
def cl_33987 : CNF.NClause := [(50,false),(71,false),(85,false),(90,false),(19,true),(74,false)]
theorem der_33987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33987 :=
  CNF.rup_sound cl_33987 [cl_28819,cl_28807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28819 v h) (hints_cons _ _ _ (der_28807 v h) (by intro d hd; cases hd)))
def cl_33988 : CNF.NClause := [(50,false),(74,false),(63,false),(85,false),(19,true),(90,false)]
theorem der_33988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33988 :=
  CNF.rup_sound cl_33988 [cl_28821,cl_26320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28821 v h) (hints_cons _ _ _ (der_26320 v h) (by intro d hd; cases hd)))
def cl_33990 : CNF.NClause := [(50,false),(90,false),(63,true),(85,false),(71,true),(74,false)]
theorem der_33990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33990 :=
  CNF.rup_sound cl_33990 [cl_28823,cl_33982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28823 v h) (hints_cons _ _ _ (der_33982 v h) (by intro d hd; cases hd)))
def cl_33994 : CNF.NClause := [(50,false),(85,false),(19,false),(63,false),(71,true),(90,false)]
theorem der_33994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33994 :=
  CNF.rup_sound cl_33994 [cl_28827,cl_28814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28827 v h) (hints_cons _ _ _ (der_28814 v h) (by intro d hd; cases hd)))
def cl_33996 : CNF.NClause := [(50,false),(71,true),(19,false),(63,true),(85,false),(90,false)]
theorem der_33996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33996 :=
  CNF.rup_sound cl_33996 [cl_28829,cl_33990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28829 v h) (hints_cons _ _ _ (der_33990 v h) (by intro d hd; cases hd)))
def cl_33998 : CNF.NClause := [(50,false),(77,false),(90,false),(71,false),(74,false),(85,true)]
theorem der_33998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33998 :=
  CNF.rup_sound cl_33998 [cl_28833,cl_28832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28833 v h) (hints_cons _ _ _ (der_28832 v h) (by intro d hd; cases hd)))
def cl_33999 : CNF.NClause := [(50,false),(77,false),(71,true),(63,false),(90,false),(74,false)]
theorem der_33999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_33999 :=
  CNF.rup_sound cl_33999 [cl_28835,cl_28834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28835 v h) (hints_cons _ _ _ (der_28834 v h) (by intro d hd; cases hd)))
def cl_34000 : CNF.NClause := [(50,false),(77,false),(19,false),(71,true),(90,false),(74,false)]
theorem der_34000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34000 :=
  CNF.rup_sound cl_34000 [cl_28836,cl_33982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28836 v h) (hints_cons _ _ _ (der_33982 v h) (by intro d hd; cases hd)))
def cl_34001 : CNF.NClause := [(50,false),(77,false),(63,true),(71,true),(90,false),(74,false)]
theorem der_34001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34001 :=
  CNF.rup_sound cl_34001 [cl_28837,cl_33982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28837 v h) (hints_cons _ _ _ (der_33982 v h) (by intro d hd; cases hd)))
def cl_34002 : CNF.NClause := [(50,false),(74,true),(77,false),(63,false),(90,false),(71,false)]
theorem der_34002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34002 :=
  CNF.rup_sound cl_34002 [cl_28838,cl_26751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28838 v h) (hints_cons _ _ _ (der_26751 v h) (by intro d hd; cases hd)))
def cl_34003 : CNF.NClause := [(50,false),(74,true),(19,false),(77,false),(90,false),(71,false)]
theorem der_34003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34003 :=
  CNF.rup_sound cl_34003 [cl_28839,cl_34002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28839 v h) (hints_cons _ _ _ (der_34002 v h) (by intro d hd; cases hd)))
def cl_34004 : CNF.NClause := [(50,false),(74,true),(63,true),(77,false),(90,false),(71,false)]
theorem der_34004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34004 :=
  CNF.rup_sound cl_34004 [cl_28840,cl_33983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28840 v h) (hints_cons _ _ _ (der_33983 v h) (by intro d hd; cases hd)))
def cl_34005 : CNF.NClause := [(50,false),(77,false),(71,true),(19,false),(63,false),(90,false)]
theorem der_34005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34005 :=
  CNF.rup_sound cl_34005 [cl_28841,cl_28814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28841 v h) (hints_cons _ _ _ (der_28814 v h) (by intro d hd; cases hd)))
def cl_34006 : CNF.NClause := [(50,false),(71,true),(77,false),(63,false),(90,false),(85,true)]
theorem der_34006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34006 :=
  CNF.rup_sound cl_34006 [cl_28842,cl_33999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28842 v h) (hints_cons _ _ _ (der_33999 v h) (by intro d hd; cases hd)))
def cl_34007 : CNF.NClause := [(50,false),(71,true),(19,false),(63,true),(77,false),(90,false)]
theorem der_34007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34007 :=
  CNF.rup_sound cl_34007 [cl_28843,cl_34000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28843 v h) (hints_cons _ _ _ (der_34000 v h) (by intro d hd; cases hd)))
def chunk021 : List CNF.NClause := [cl_33427,cl_33429,cl_33430,cl_33431,cl_33432,cl_33433,cl_33434,cl_33435,cl_33436,cl_33437,cl_33438,cl_33439,cl_33440,cl_33441,cl_33442,cl_33443,cl_33444,cl_33445,cl_33446,cl_33447,cl_33448,cl_33449,cl_33450,cl_33451,cl_33452,cl_33453,cl_33454,cl_33455,cl_33456,cl_33457,cl_33458,cl_33459,cl_33460,cl_33461,cl_33462,cl_33464,cl_33465,cl_33466,cl_33467,cl_33468,cl_33469,cl_33470,cl_33471,cl_33472,cl_33473,cl_33474,cl_33475,cl_33476,cl_33477,cl_33478,cl_33479,cl_33480,cl_33481,cl_33482,cl_33483,cl_33484,cl_33485,cl_33486,cl_33487,cl_33488,cl_33489,cl_33490,cl_33491,cl_33492,cl_33493,cl_33494,cl_33495,cl_33497,cl_33498,cl_33499,cl_33500,cl_33501,cl_33502,cl_33503,cl_33505,cl_33506,cl_33507,cl_33508,cl_33509,cl_33510,cl_33511,cl_33512,cl_33513,cl_33514,cl_33515,cl_33517,cl_33518,cl_33519,cl_33520,cl_33521,cl_33522,cl_33523,cl_33524,cl_33526,cl_33527,cl_33528,cl_33529,cl_33530,cl_33531,cl_33532,cl_33533,cl_33534,cl_33535,cl_33537,cl_33538,cl_33539,cl_33540,cl_33541,cl_33542,cl_33543,cl_33544,cl_33545,cl_33546,cl_33547,cl_33548,cl_33549,cl_33550,cl_33551,cl_33552,cl_33554,cl_33555,cl_33556,cl_33557,cl_33558,cl_33559,cl_33560,cl_33561,cl_33562,cl_33563,cl_33564,cl_33565,cl_33566,cl_33567,cl_33568,cl_33569,cl_33570,cl_33571,cl_33572,cl_33573,cl_33574,cl_33575,cl_33576,cl_33577,cl_33578,cl_33579,cl_33580,cl_33581,cl_33582,cl_33583,cl_33584,cl_33585,cl_33588,cl_33589,cl_33590,cl_33591,cl_33592,cl_33593,cl_33594,cl_33595,cl_33596,cl_33597,cl_33601,cl_33606,cl_33608,cl_33609,cl_33610,cl_33611,cl_33612,cl_33613,cl_33615,cl_33616,cl_33617,cl_33618,cl_33619,cl_33620,cl_33621,cl_33622,cl_33623,cl_33625,cl_33626,cl_33628,cl_33629,cl_33630,cl_33631,cl_33632,cl_33633,cl_33634,cl_33635,cl_33636,cl_33637,cl_33638,cl_33639,cl_33640,cl_33641,cl_33642,cl_33644,cl_33645,cl_33646,cl_33648,cl_33649,cl_33650,cl_33651,cl_33652,cl_33653,cl_33654,cl_33655,cl_33656,cl_33657,cl_33658,cl_33659,cl_33660,cl_33661,cl_33662,cl_33663,cl_33664,cl_33665,cl_33666,cl_33667,cl_33668,cl_33669,cl_33670,cl_33671,cl_33672,cl_33673,cl_33674,cl_33675,cl_33676,cl_33677,cl_33679,cl_33680,cl_33681,cl_33682,cl_33683,cl_33684,cl_33685,cl_33686,cl_33687,cl_33688,cl_33689,cl_33690,cl_33691,cl_33692,cl_33693,cl_33694,cl_33695,cl_33696,cl_33697,cl_33698,cl_33699,cl_33700,cl_33701,cl_33702,cl_33704,cl_33709,cl_33710,cl_33711,cl_33713,cl_33714,cl_33715,cl_33717,cl_33718,cl_33720,cl_33723,cl_33724,cl_33725,cl_33726,cl_33727,cl_33728,cl_33729,cl_33730,cl_33731,cl_33732,cl_33733,cl_33734,cl_33736,cl_33738,cl_33739,cl_33740,cl_33741,cl_33742,cl_33743,cl_33744,cl_33748,cl_33749,cl_33750,cl_33751,cl_33752,cl_33753,cl_33754,cl_33755,cl_33756,cl_33757,cl_33759,cl_33760,cl_33761,cl_33762,cl_33763,cl_33765,cl_33766,cl_33767,cl_33768,cl_33769,cl_33770,cl_33771,cl_33772,cl_33773,cl_33774,cl_33775,cl_33776,cl_33777,cl_33778,cl_33779,cl_33780,cl_33781,cl_33782,cl_33783,cl_33784,cl_33785,cl_33786,cl_33787,cl_33788,cl_33789,cl_33790,cl_33791,cl_33792,cl_33793,cl_33794,cl_33795,cl_33796,cl_33797,cl_33802,cl_33803,cl_33804,cl_33806,cl_33807,cl_33808,cl_33810,cl_33811,cl_33816,cl_33817,cl_33818,cl_33820,cl_33821,cl_33822,cl_33823,cl_33824,cl_33825,cl_33826,cl_33827,cl_33829,cl_33830,cl_33831,cl_33833,cl_33834,cl_33835,cl_33836,cl_33838,cl_33839,cl_33840,cl_33841,cl_33842,cl_33843,cl_33844,cl_33845,cl_33847,cl_33848,cl_33849,cl_33850,cl_33851,cl_33852,cl_33853,cl_33854,cl_33855,cl_33856,cl_33857,cl_33858,cl_33859,cl_33860,cl_33862,cl_33863,cl_33864,cl_33865,cl_33866,cl_33867,cl_33868,cl_33870,cl_33871,cl_33874,cl_33875,cl_33876,cl_33877,cl_33878,cl_33879,cl_33882,cl_33883,cl_33885,cl_33887,cl_33888,cl_33889,cl_33890,cl_33891,cl_33892,cl_33893,cl_33894,cl_33895,cl_33897,cl_33899,cl_33901,cl_33902,cl_33903,cl_33904,cl_33905,cl_33906,cl_33907,cl_33908,cl_33909,cl_33910,cl_33911,cl_33912,cl_33913,cl_33914,cl_33916,cl_33917,cl_33918,cl_33919,cl_33920,cl_33921,cl_33922,cl_33924,cl_33925,cl_33926,cl_33927,cl_33928,cl_33929,cl_33930,cl_33931,cl_33932,cl_33933,cl_33934,cl_33935,cl_33936,cl_33937,cl_33938,cl_33939,cl_33940,cl_33941,cl_33942,cl_33943,cl_33944,cl_33945,cl_33946,cl_33947,cl_33948,cl_33949,cl_33950,cl_33951,cl_33952,cl_33953,cl_33955,cl_33956,cl_33957,cl_33958,cl_33959,cl_33960,cl_33961,cl_33962,cl_33963,cl_33964,cl_33965,cl_33966,cl_33967,cl_33968,cl_33970,cl_33972,cl_33973,cl_33974,cl_33976,cl_33977,cl_33978,cl_33979,cl_33980,cl_33982,cl_33983,cl_33984,cl_33985,cl_33987,cl_33988,cl_33990,cl_33994,cl_33996,cl_33998,cl_33999,cl_34000,cl_34001,cl_34002,cl_34003,cl_34004,cl_34005,cl_34006,cl_34007]
theorem chunk_sound021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk021, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_33427 v h) (hints_cons _ _ _ (der_33429 v h) (hints_cons _ _ _ (der_33430 v h) (hints_cons _ _ _ (der_33431 v h) (hints_cons _ _ _ (der_33432 v h) (hints_cons _ _ _ (der_33433 v h) (hints_cons _ _ _ (der_33434 v h) (hints_cons _ _ _ (der_33435 v h) (hints_cons _ _ _ (der_33436 v h) (hints_cons _ _ _ (der_33437 v h) (hints_cons _ _ _ (der_33438 v h) (hints_cons _ _ _ (der_33439 v h) (hints_cons _ _ _ (der_33440 v h) (hints_cons _ _ _ (der_33441 v h) (hints_cons _ _ _ (der_33442 v h) (hints_cons _ _ _ (der_33443 v h) (hints_cons _ _ _ (der_33444 v h) (hints_cons _ _ _ (der_33445 v h) (hints_cons _ _ _ (der_33446 v h) (hints_cons _ _ _ (der_33447 v h) (hints_cons _ _ _ (der_33448 v h) (hints_cons _ _ _ (der_33449 v h) (hints_cons _ _ _ (der_33450 v h) (hints_cons _ _ _ (der_33451 v h) (hints_cons _ _ _ (der_33452 v h) (hints_cons _ _ _ (der_33453 v h) (hints_cons _ _ _ (der_33454 v h) (hints_cons _ _ _ (der_33455 v h) (hints_cons _ _ _ (der_33456 v h) (hints_cons _ _ _ (der_33457 v h) (hints_cons _ _ _ (der_33458 v h) (hints_cons _ _ _ (der_33459 v h) (hints_cons _ _ _ (der_33460 v h) (hints_cons _ _ _ (der_33461 v h) (hints_cons _ _ _ (der_33462 v h) (hints_cons _ _ _ (der_33464 v h) (hints_cons _ _ _ (der_33465 v h) (hints_cons _ _ _ (der_33466 v h) (hints_cons _ _ _ (der_33467 v h) (hints_cons _ _ _ (der_33468 v h) (hints_cons _ _ _ (der_33469 v h) (hints_cons _ _ _ (der_33470 v h) (hints_cons _ _ _ (der_33471 v h) (hints_cons _ _ _ (der_33472 v h) (hints_cons _ _ _ (der_33473 v h) (hints_cons _ _ _ (der_33474 v h) (hints_cons _ _ _ (der_33475 v h) (hints_cons _ _ _ (der_33476 v h) (hints_cons _ _ _ (der_33477 v h) (hints_cons _ _ _ (der_33478 v h) (hints_cons _ _ _ (der_33479 v h) (hints_cons _ _ _ (der_33480 v h) (hints_cons _ _ _ (der_33481 v h) (hints_cons _ _ _ (der_33482 v h) (hints_cons _ _ _ (der_33483 v h) (hints_cons _ _ _ (der_33484 v h) (hints_cons _ _ _ (der_33485 v h) (hints_cons _ _ _ (der_33486 v h) (hints_cons _ _ _ (der_33487 v h) (hints_cons _ _ _ (der_33488 v h) (hints_cons _ _ _ (der_33489 v h) (hints_cons _ _ _ (der_33490 v h) (hints_cons _ _ _ (der_33491 v h) (hints_cons _ _ _ (der_33492 v h) (hints_cons _ _ _ (der_33493 v h) (hints_cons _ _ _ (der_33494 v h) (hints_cons _ _ _ (der_33495 v h) (hints_cons _ _ _ (der_33497 v h) (hints_cons _ _ _ (der_33498 v h) (hints_cons _ _ _ (der_33499 v h) (hints_cons _ _ _ (der_33500 v h) (hints_cons _ _ _ (der_33501 v h) (hints_cons _ _ _ (der_33502 v h) (hints_cons _ _ _ (der_33503 v h) (hints_cons _ _ _ (der_33505 v h) (hints_cons _ _ _ (der_33506 v h) (hints_cons _ _ _ (der_33507 v h) (hints_cons _ _ _ (der_33508 v h) (hints_cons _ _ _ (der_33509 v h) (hints_cons _ _ _ (der_33510 v h) (hints_cons _ _ _ (der_33511 v h) (hints_cons _ _ _ (der_33512 v h) (hints_cons _ _ _ (der_33513 v h) (hints_cons _ _ _ (der_33514 v h) (hints_cons _ _ _ (der_33515 v h) (hints_cons _ _ _ (der_33517 v h) (hints_cons _ _ _ (der_33518 v h) (hints_cons _ _ _ (der_33519 v h) (hints_cons _ _ _ (der_33520 v h) (hints_cons _ _ _ (der_33521 v h) (hints_cons _ _ _ (der_33522 v h) (hints_cons _ _ _ (der_33523 v h) (hints_cons _ _ _ (der_33524 v h) (hints_cons _ _ _ (der_33526 v h) (hints_cons _ _ _ (der_33527 v h) (hints_cons _ _ _ (der_33528 v h) (hints_cons _ _ _ (der_33529 v h) (hints_cons _ _ _ (der_33530 v h) (hints_cons _ _ _ (der_33531 v h) (hints_cons _ _ _ (der_33532 v h) (hints_cons _ _ _ (der_33533 v h) (hints_cons _ _ _ (der_33534 v h) (hints_cons _ _ _ (der_33535 v h) (hints_cons _ _ _ (der_33537 v h) (hints_cons _ _ _ (der_33538 v h) (hints_cons _ _ _ (der_33539 v h) (hints_cons _ _ _ (der_33540 v h) (hints_cons _ _ _ (der_33541 v h) (hints_cons _ _ _ (der_33542 v h) (hints_cons _ _ _ (der_33543 v h) (hints_cons _ _ _ (der_33544 v h) (hints_cons _ _ _ (der_33545 v h) (hints_cons _ _ _ (der_33546 v h) (hints_cons _ _ _ (der_33547 v h) (hints_cons _ _ _ (der_33548 v h) (hints_cons _ _ _ (der_33549 v h) (hints_cons _ _ _ (der_33550 v h) (hints_cons _ _ _ (der_33551 v h) (hints_cons _ _ _ (der_33552 v h) (hints_cons _ _ _ (der_33554 v h) (hints_cons _ _ _ (der_33555 v h) (hints_cons _ _ _ (der_33556 v h) (hints_cons _ _ _ (der_33557 v h) (hints_cons _ _ _ (der_33558 v h) (hints_cons _ _ _ (der_33559 v h) (hints_cons _ _ _ (der_33560 v h) (hints_cons _ _ _ (der_33561 v h) (hints_cons _ _ _ (der_33562 v h) (hints_cons _ _ _ (der_33563 v h) (hints_cons _ _ _ (der_33564 v h) (hints_cons _ _ _ (der_33565 v h) (hints_cons _ _ _ (der_33566 v h) (hints_cons _ _ _ (der_33567 v h) (hints_cons _ _ _ (der_33568 v h) (hints_cons _ _ _ (der_33569 v h) (hints_cons _ _ _ (der_33570 v h) (hints_cons _ _ _ (der_33571 v h) (hints_cons _ _ _ (der_33572 v h) (hints_cons _ _ _ (der_33573 v h) (hints_cons _ _ _ (der_33574 v h) (hints_cons _ _ _ (der_33575 v h) (hints_cons _ _ _ (der_33576 v h) (hints_cons _ _ _ (der_33577 v h) (hints_cons _ _ _ (der_33578 v h) (hints_cons _ _ _ (der_33579 v h) (hints_cons _ _ _ (der_33580 v h) (hints_cons _ _ _ (der_33581 v h) (hints_cons _ _ _ (der_33582 v h) (hints_cons _ _ _ (der_33583 v h) (hints_cons _ _ _ (der_33584 v h) (hints_cons _ _ _ (der_33585 v h) (hints_cons _ _ _ (der_33588 v h) (hints_cons _ _ _ (der_33589 v h) (hints_cons _ _ _ (der_33590 v h) (hints_cons _ _ _ (der_33591 v h) (hints_cons _ _ _ (der_33592 v h) (hints_cons _ _ _ (der_33593 v h) (hints_cons _ _ _ (der_33594 v h) (hints_cons _ _ _ (der_33595 v h) (hints_cons _ _ _ (der_33596 v h) (hints_cons _ _ _ (der_33597 v h) (hints_cons _ _ _ (der_33601 v h) (hints_cons _ _ _ (der_33606 v h) (hints_cons _ _ _ (der_33608 v h) (hints_cons _ _ _ (der_33609 v h) (hints_cons _ _ _ (der_33610 v h) (hints_cons _ _ _ (der_33611 v h) (hints_cons _ _ _ (der_33612 v h) (hints_cons _ _ _ (der_33613 v h) (hints_cons _ _ _ (der_33615 v h) (hints_cons _ _ _ (der_33616 v h) (hints_cons _ _ _ (der_33617 v h) (hints_cons _ _ _ (der_33618 v h) (hints_cons _ _ _ (der_33619 v h) (hints_cons _ _ _ (der_33620 v h) (hints_cons _ _ _ (der_33621 v h) (hints_cons _ _ _ (der_33622 v h) (hints_cons _ _ _ (der_33623 v h) (hints_cons _ _ _ (der_33625 v h) (hints_cons _ _ _ (der_33626 v h) (hints_cons _ _ _ (der_33628 v h) (hints_cons _ _ _ (der_33629 v h) (hints_cons _ _ _ (der_33630 v h) (hints_cons _ _ _ (der_33631 v h) (hints_cons _ _ _ (der_33632 v h) (hints_cons _ _ _ (der_33633 v h) (hints_cons _ _ _ (der_33634 v h) (hints_cons _ _ _ (der_33635 v h) (hints_cons _ _ _ (der_33636 v h) (hints_cons _ _ _ (der_33637 v h) (hints_cons _ _ _ (der_33638 v h) (hints_cons _ _ _ (der_33639 v h) (hints_cons _ _ _ (der_33640 v h) (hints_cons _ _ _ (der_33641 v h) (hints_cons _ _ _ (der_33642 v h) (hints_cons _ _ _ (der_33644 v h) (hints_cons _ _ _ (der_33645 v h) (hints_cons _ _ _ (der_33646 v h) (hints_cons _ _ _ (der_33648 v h) (hints_cons _ _ _ (der_33649 v h) (hints_cons _ _ _ (der_33650 v h) (hints_cons _ _ _ (der_33651 v h) (hints_cons _ _ _ (der_33652 v h) (hints_cons _ _ _ (der_33653 v h) (hints_cons _ _ _ (der_33654 v h) (hints_cons _ _ _ (der_33655 v h) (hints_cons _ _ _ (der_33656 v h) (hints_cons _ _ _ (der_33657 v h) (hints_cons _ _ _ (der_33658 v h) (hints_cons _ _ _ (der_33659 v h) (hints_cons _ _ _ (der_33660 v h) (hints_cons _ _ _ (der_33661 v h) (hints_cons _ _ _ (der_33662 v h) (hints_cons _ _ _ (der_33663 v h) (hints_cons _ _ _ (der_33664 v h) (hints_cons _ _ _ (der_33665 v h) (hints_cons _ _ _ (der_33666 v h) (hints_cons _ _ _ (der_33667 v h) (hints_cons _ _ _ (der_33668 v h) (hints_cons _ _ _ (der_33669 v h) (hints_cons _ _ _ (der_33670 v h) (hints_cons _ _ _ (der_33671 v h) (hints_cons _ _ _ (der_33672 v h) (hints_cons _ _ _ (der_33673 v h) (hints_cons _ _ _ (der_33674 v h) (hints_cons _ _ _ (der_33675 v h) (hints_cons _ _ _ (der_33676 v h) (hints_cons _ _ _ (der_33677 v h) (hints_cons _ _ _ (der_33679 v h) (hints_cons _ _ _ (der_33680 v h) (hints_cons _ _ _ (der_33681 v h) (hints_cons _ _ _ (der_33682 v h) (hints_cons _ _ _ (der_33683 v h) (hints_cons _ _ _ (der_33684 v h) (hints_cons _ _ _ (der_33685 v h) (hints_cons _ _ _ (der_33686 v h) (hints_cons _ _ _ (der_33687 v h) (hints_cons _ _ _ (der_33688 v h) (hints_cons _ _ _ (der_33689 v h) (hints_cons _ _ _ (der_33690 v h) (hints_cons _ _ _ (der_33691 v h) (hints_cons _ _ _ (der_33692 v h) (hints_cons _ _ _ (der_33693 v h) (hints_cons _ _ _ (der_33694 v h) (hints_cons _ _ _ (der_33695 v h) (hints_cons _ _ _ (der_33696 v h) (hints_cons _ _ _ (der_33697 v h) (hints_cons _ _ _ (der_33698 v h) (hints_cons _ _ _ (der_33699 v h) (hints_cons _ _ _ (der_33700 v h) (hints_cons _ _ _ (der_33701 v h) (hints_cons _ _ _ (der_33702 v h) (hints_cons _ _ _ (der_33704 v h) (hints_cons _ _ _ (der_33709 v h) (hints_cons _ _ _ (der_33710 v h) (hints_cons _ _ _ (der_33711 v h) (hints_cons _ _ _ (der_33713 v h) (hints_cons _ _ _ (der_33714 v h) (hints_cons _ _ _ (der_33715 v h) (hints_cons _ _ _ (der_33717 v h) (hints_cons _ _ _ (der_33718 v h) (hints_cons _ _ _ (der_33720 v h) (hints_cons _ _ _ (der_33723 v h) (hints_cons _ _ _ (der_33724 v h) (hints_cons _ _ _ (der_33725 v h) (hints_cons _ _ _ (der_33726 v h) (hints_cons _ _ _ (der_33727 v h) (hints_cons _ _ _ (der_33728 v h) (hints_cons _ _ _ (der_33729 v h) (hints_cons _ _ _ (der_33730 v h) (hints_cons _ _ _ (der_33731 v h) (hints_cons _ _ _ (der_33732 v h) (hints_cons _ _ _ (der_33733 v h) (hints_cons _ _ _ (der_33734 v h) (hints_cons _ _ _ (der_33736 v h) (hints_cons _ _ _ (der_33738 v h) (hints_cons _ _ _ (der_33739 v h) (hints_cons _ _ _ (der_33740 v h) (hints_cons _ _ _ (der_33741 v h) (hints_cons _ _ _ (der_33742 v h) (hints_cons _ _ _ (der_33743 v h) (hints_cons _ _ _ (der_33744 v h) (hints_cons _ _ _ (der_33748 v h) (hints_cons _ _ _ (der_33749 v h) (hints_cons _ _ _ (der_33750 v h) (hints_cons _ _ _ (der_33751 v h) (hints_cons _ _ _ (der_33752 v h) (hints_cons _ _ _ (der_33753 v h) (hints_cons _ _ _ (der_33754 v h) (hints_cons _ _ _ (der_33755 v h) (hints_cons _ _ _ (der_33756 v h) (hints_cons _ _ _ (der_33757 v h) (hints_cons _ _ _ (der_33759 v h) (hints_cons _ _ _ (der_33760 v h) (hints_cons _ _ _ (der_33761 v h) (hints_cons _ _ _ (der_33762 v h) (hints_cons _ _ _ (der_33763 v h) (hints_cons _ _ _ (der_33765 v h) (hints_cons _ _ _ (der_33766 v h) (hints_cons _ _ _ (der_33767 v h) (hints_cons _ _ _ (der_33768 v h) (hints_cons _ _ _ (der_33769 v h) (hints_cons _ _ _ (der_33770 v h) (hints_cons _ _ _ (der_33771 v h) (hints_cons _ _ _ (der_33772 v h) (hints_cons _ _ _ (der_33773 v h) (hints_cons _ _ _ (der_33774 v h) (hints_cons _ _ _ (der_33775 v h) (hints_cons _ _ _ (der_33776 v h) (hints_cons _ _ _ (der_33777 v h) (hints_cons _ _ _ (der_33778 v h) (hints_cons _ _ _ (der_33779 v h) (hints_cons _ _ _ (der_33780 v h) (hints_cons _ _ _ (der_33781 v h) (hints_cons _ _ _ (der_33782 v h) (hints_cons _ _ _ (der_33783 v h) (hints_cons _ _ _ (der_33784 v h) (hints_cons _ _ _ (der_33785 v h) (hints_cons _ _ _ (der_33786 v h) (hints_cons _ _ _ (der_33787 v h) (hints_cons _ _ _ (der_33788 v h) (hints_cons _ _ _ (der_33789 v h) (hints_cons _ _ _ (der_33790 v h) (hints_cons _ _ _ (der_33791 v h) (hints_cons _ _ _ (der_33792 v h) (hints_cons _ _ _ (der_33793 v h) (hints_cons _ _ _ (der_33794 v h) (hints_cons _ _ _ (der_33795 v h) (hints_cons _ _ _ (der_33796 v h) (hints_cons _ _ _ (der_33797 v h) (hints_cons _ _ _ (der_33802 v h) (hints_cons _ _ _ (der_33803 v h) (hints_cons _ _ _ (der_33804 v h) (hints_cons _ _ _ (der_33806 v h) (hints_cons _ _ _ (der_33807 v h) (hints_cons _ _ _ (der_33808 v h) (hints_cons _ _ _ (der_33810 v h) (hints_cons _ _ _ (der_33811 v h) (hints_cons _ _ _ (der_33816 v h) (hints_cons _ _ _ (der_33817 v h) (hints_cons _ _ _ (der_33818 v h) (hints_cons _ _ _ (der_33820 v h) (hints_cons _ _ _ (der_33821 v h) (hints_cons _ _ _ (der_33822 v h) (hints_cons _ _ _ (der_33823 v h) (hints_cons _ _ _ (der_33824 v h) (hints_cons _ _ _ (der_33825 v h) (hints_cons _ _ _ (der_33826 v h) (hints_cons _ _ _ (der_33827 v h) (hints_cons _ _ _ (der_33829 v h) (hints_cons _ _ _ (der_33830 v h) (hints_cons _ _ _ (der_33831 v h) (hints_cons _ _ _ (der_33833 v h) (hints_cons _ _ _ (der_33834 v h) (hints_cons _ _ _ (der_33835 v h) (hints_cons _ _ _ (der_33836 v h) (hints_cons _ _ _ (der_33838 v h) (hints_cons _ _ _ (der_33839 v h) (hints_cons _ _ _ (der_33840 v h) (hints_cons _ _ _ (der_33841 v h) (hints_cons _ _ _ (der_33842 v h) (hints_cons _ _ _ (der_33843 v h) (hints_cons _ _ _ (der_33844 v h) (hints_cons _ _ _ (der_33845 v h) (hints_cons _ _ _ (der_33847 v h) (hints_cons _ _ _ (der_33848 v h) (hints_cons _ _ _ (der_33849 v h) (hints_cons _ _ _ (der_33850 v h) (hints_cons _ _ _ (der_33851 v h) (hints_cons _ _ _ (der_33852 v h) (hints_cons _ _ _ (der_33853 v h) (hints_cons _ _ _ (der_33854 v h) (hints_cons _ _ _ (der_33855 v h) (hints_cons _ _ _ (der_33856 v h) (hints_cons _ _ _ (der_33857 v h) (hints_cons _ _ _ (der_33858 v h) (hints_cons _ _ _ (der_33859 v h) (hints_cons _ _ _ (der_33860 v h) (hints_cons _ _ _ (der_33862 v h) (hints_cons _ _ _ (der_33863 v h) (hints_cons _ _ _ (der_33864 v h) (hints_cons _ _ _ (der_33865 v h) (hints_cons _ _ _ (der_33866 v h) (hints_cons _ _ _ (der_33867 v h) (hints_cons _ _ _ (der_33868 v h) (hints_cons _ _ _ (der_33870 v h) (hints_cons _ _ _ (der_33871 v h) (hints_cons _ _ _ (der_33874 v h) (hints_cons _ _ _ (der_33875 v h) (hints_cons _ _ _ (der_33876 v h) (hints_cons _ _ _ (der_33877 v h) (hints_cons _ _ _ (der_33878 v h) (hints_cons _ _ _ (der_33879 v h) (hints_cons _ _ _ (der_33882 v h) (hints_cons _ _ _ (der_33883 v h) (hints_cons _ _ _ (der_33885 v h) (hints_cons _ _ _ (der_33887 v h) (hints_cons _ _ _ (der_33888 v h) (hints_cons _ _ _ (der_33889 v h) (hints_cons _ _ _ (der_33890 v h) (hints_cons _ _ _ (der_33891 v h) (hints_cons _ _ _ (der_33892 v h) (hints_cons _ _ _ (der_33893 v h) (hints_cons _ _ _ (der_33894 v h) (hints_cons _ _ _ (der_33895 v h) (hints_cons _ _ _ (der_33897 v h) (hints_cons _ _ _ (der_33899 v h) (hints_cons _ _ _ (der_33901 v h) (hints_cons _ _ _ (der_33902 v h) (hints_cons _ _ _ (der_33903 v h) (hints_cons _ _ _ (der_33904 v h) (hints_cons _ _ _ (der_33905 v h) (hints_cons _ _ _ (der_33906 v h) (hints_cons _ _ _ (der_33907 v h) (hints_cons _ _ _ (der_33908 v h) (hints_cons _ _ _ (der_33909 v h) (hints_cons _ _ _ (der_33910 v h) (hints_cons _ _ _ (der_33911 v h) (hints_cons _ _ _ (der_33912 v h) (hints_cons _ _ _ (der_33913 v h) (hints_cons _ _ _ (der_33914 v h) (hints_cons _ _ _ (der_33916 v h) (hints_cons _ _ _ (der_33917 v h) (hints_cons _ _ _ (der_33918 v h) (hints_cons _ _ _ (der_33919 v h) (hints_cons _ _ _ (der_33920 v h) (hints_cons _ _ _ (der_33921 v h) (hints_cons _ _ _ (der_33922 v h) (hints_cons _ _ _ (der_33924 v h) (hints_cons _ _ _ (der_33925 v h) (hints_cons _ _ _ (der_33926 v h) (hints_cons _ _ _ (der_33927 v h) (hints_cons _ _ _ (der_33928 v h) (hints_cons _ _ _ (der_33929 v h) (hints_cons _ _ _ (der_33930 v h) (hints_cons _ _ _ (der_33931 v h) (hints_cons _ _ _ (der_33932 v h) (hints_cons _ _ _ (der_33933 v h) (hints_cons _ _ _ (der_33934 v h) (hints_cons _ _ _ (der_33935 v h) (hints_cons _ _ _ (der_33936 v h) (hints_cons _ _ _ (der_33937 v h) (hints_cons _ _ _ (der_33938 v h) (hints_cons _ _ _ (der_33939 v h) (hints_cons _ _ _ (der_33940 v h) (hints_cons _ _ _ (der_33941 v h) (hints_cons _ _ _ (der_33942 v h) (hints_cons _ _ _ (der_33943 v h) (hints_cons _ _ _ (der_33944 v h) (hints_cons _ _ _ (der_33945 v h) (hints_cons _ _ _ (der_33946 v h) (hints_cons _ _ _ (der_33947 v h) (hints_cons _ _ _ (der_33948 v h) (hints_cons _ _ _ (der_33949 v h) (hints_cons _ _ _ (der_33950 v h) (hints_cons _ _ _ (der_33951 v h) (hints_cons _ _ _ (der_33952 v h) (hints_cons _ _ _ (der_33953 v h) (hints_cons _ _ _ (der_33955 v h) (hints_cons _ _ _ (der_33956 v h) (hints_cons _ _ _ (der_33957 v h) (hints_cons _ _ _ (der_33958 v h) (hints_cons _ _ _ (der_33959 v h) (hints_cons _ _ _ (der_33960 v h) (hints_cons _ _ _ (der_33961 v h) (hints_cons _ _ _ (der_33962 v h) (hints_cons _ _ _ (der_33963 v h) (hints_cons _ _ _ (der_33964 v h) (hints_cons _ _ _ (der_33965 v h) (hints_cons _ _ _ (der_33966 v h) (hints_cons _ _ _ (der_33967 v h) (hints_cons _ _ _ (der_33968 v h) (hints_cons _ _ _ (der_33970 v h) (hints_cons _ _ _ (der_33972 v h) (hints_cons _ _ _ (der_33973 v h) (hints_cons _ _ _ (der_33974 v h) (hints_cons _ _ _ (der_33976 v h) (hints_cons _ _ _ (der_33977 v h) (hints_cons _ _ _ (der_33978 v h) (hints_cons _ _ _ (der_33979 v h) (hints_cons _ _ _ (der_33980 v h) (hints_cons _ _ _ (der_33982 v h) (hints_cons _ _ _ (der_33983 v h) (hints_cons _ _ _ (der_33984 v h) (hints_cons _ _ _ (der_33985 v h) (hints_cons _ _ _ (der_33987 v h) (hints_cons _ _ _ (der_33988 v h) (hints_cons _ _ _ (der_33990 v h) (hints_cons _ _ _ (der_33994 v h) (hints_cons _ _ _ (der_33996 v h) (hints_cons _ _ _ (der_33998 v h) (hints_cons _ _ _ (der_33999 v h) (hints_cons _ _ _ (der_34000 v h) (hints_cons _ _ _ (der_34001 v h) (hints_cons _ _ _ (der_34002 v h) (hints_cons _ _ _ (der_34003 v h) (hints_cons _ _ _ (der_34004 v h) (hints_cons _ _ _ (der_34005 v h) (hints_cons _ _ _ (der_34006 v h) (hints_cons _ _ _ (der_34007 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix021 := prefix020 ++ chunk021
theorem prefix_sound021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix021, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound020 v h c hc
  · exact chunk_sound021 v h c hc
end Percolation.NReplay
