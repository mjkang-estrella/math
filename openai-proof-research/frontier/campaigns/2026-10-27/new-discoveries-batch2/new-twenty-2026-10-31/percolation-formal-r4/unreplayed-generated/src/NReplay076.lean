import NReplay075
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_77527 : CNF.NClause := [(26,false),(4,false),(5,true),(83,true)]
theorem der_77527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77527 :=
  CNF.rup_sound cl_77527 [cl_60777,cl_77269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60777 v h) (hints_cons _ _ _ (der_77269 v h) (by intro d hd; cases hd)))
def cl_77529 : CNF.NClause := [(46,true),(5,false),(139,false),(18,false)]
theorem der_77529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77529 :=
  CNF.rup_sound cl_77529 [cl_61876,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61876 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_77530 : CNF.NClause := [(921,false),(67,true),(920,true),(919,true)]
theorem der_77530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77530 :=
  CNF.rup_sound cl_77530 [cl_62068,cl_62077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62068 v h) (hints_cons _ _ _ (der_62077 v h) (by intro d hd; cases hd)))
def cl_77531 : CNF.NClause := [(73,true),(483,false),(11,true),(7,true)]
theorem der_77531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77531 :=
  CNF.rup_sound cl_77531 [cl_63960,cl_14113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63960 v h) (hints_cons _ _ _ (inp_14113 v h) (by intro d hd; cases hd)))
def cl_77533 : CNF.NClause := [(83,true),(5,false),(17,true),(11,false)]
theorem der_77533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77533 :=
  CNF.rup_sound cl_77533 [cl_61760,cl_62292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61760 v h) (hints_cons _ _ _ (der_62292 v h) (by intro d hd; cases hd)))
def cl_77534 : CNF.NClause := [(138,false),(45,true),(7,false),(129,true)]
theorem der_77534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77534 :=
  CNF.rup_sound cl_77534 [cl_60805,cl_76534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60805 v h) (hints_cons _ _ _ (der_76534 v h) (by intro d hd; cases hd)))
def cl_77535 : CNF.NClause := [(27,false),(2,false),(69,true),(11,true)]
theorem der_77535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77535 :=
  CNF.rup_sound cl_77535 [cl_61019,cl_56890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61019 v h) (hints_cons _ _ _ (der_56890 v h) (by intro d hd; cases hd)))
def cl_77536 : CNF.NClause := [(17,false),(4,false),(83,true),(23,true)]
theorem der_77536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77536 :=
  CNF.rup_sound cl_77536 [cl_62690,cl_62292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62690 v h) (hints_cons _ _ _ (der_62292 v h) (by intro d hd; cases hd)))
def cl_77537 : CNF.NClause := [(482,false),(10,true),(11,true),(76,true)]
theorem der_77537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77537 :=
  CNF.rup_sound cl_77537 [cl_63255,cl_14112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63255 v h) (hints_cons _ _ _ (inp_14112 v h) (by intro d hd; cases hd)))
def cl_77538 : CNF.NClause := [(135,false),(80,true),(29,true),(7,true)]
theorem der_77538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77538 :=
  CNF.rup_sound cl_77538 [cl_61578,cl_15777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61578 v h) (hints_cons _ _ _ (der_15777 v h) (by intro d hd; cases hd)))
def cl_77539 : CNF.NClause := [(912,false),(904,true),(84,true),(915,true)]
theorem der_77539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77539 :=
  CNF.rup_sound cl_77539 [cl_61242,cl_15879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61242 v h) (hints_cons _ _ _ (der_15879 v h) (by intro d hd; cases hd)))
def cl_77540 : CNF.NClause := [(69,true),(908,false),(926,true),(917,true)]
theorem der_77540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77540 :=
  CNF.rup_sound cl_77540 [cl_61265,cl_15875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61265 v h) (hints_cons _ _ _ (der_15875 v h) (by intro d hd; cases hd)))
def cl_77541 : CNF.NClause := [(763,false),(20,true),(85,true),(27,true)]
theorem der_77541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77541 :=
  CNF.rup_sound cl_77541 [cl_63872,cl_14385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63872 v h) (hints_cons _ _ _ (inp_14385 v h) (by intro d hd; cases hd)))
def cl_77542 : CNF.NClause := [(82,true),(133,false),(81,false),(88,false)]
theorem der_77542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77542 :=
  CNF.rup_sound cl_77542 [cl_62190,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62190 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_77543 : CNF.NClause := [(920,false),(922,true),(67,true),(923,true)]
theorem der_77543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77543 :=
  CNF.rup_sound cl_77543 [cl_60619,cl_15887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60619 v h) (hints_cons _ _ _ (der_15887 v h) (by intro d hd; cases hd)))
def cl_77544 : CNF.NClause := [(1076,true),(67,true),(1074,true),(22,false)]
theorem der_77544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77544 :=
  CNF.rup_sound cl_77544 [cl_61002,cl_49872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61002 v h) (hints_cons _ _ _ (der_49872 v h) (by intro d hd; cases hd)))
def cl_77546 : CNF.NClause := [(918,false),(919,true),(71,true),(7,true)]
theorem der_77546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77546 :=
  CNF.rup_sound cl_77546 [cl_63921,cl_15885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63921 v h) (hints_cons _ _ _ (der_15885 v h) (by intro d hd; cases hd)))
def cl_77547 : CNF.NClause := [(39,true),(132,false),(76,false),(90,false)]
theorem der_77547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77547 :=
  CNF.rup_sound cl_77547 [cl_65997,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65997 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_77549 : CNF.NClause := [(999,false),(19,true),(28,true),(71,true)]
theorem der_77549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77549 :=
  CNF.rup_sound cl_77549 [cl_70695,cl_14613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70695 v h) (hints_cons _ _ _ (inp_14613 v h) (by intro d hd; cases hd)))
def cl_77550 : CNF.NClause := [(148,false),(80,true),(131,true),(135,true)]
theorem der_77550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77550 :=
  CNF.rup_sound cl_77550 [cl_71697,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71697 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_77551 : CNF.NClause := [(1074,false),(16,true),(68,true),(8,true)]
theorem der_77551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77551 :=
  CNF.rup_sound cl_77551 [cl_73356,cl_15922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73356 v h) (hints_cons _ _ _ (der_15922 v h) (by intro d hd; cases hd)))
def cl_77554 : CNF.NClause := [(44,false),(88,true),(84,false),(78,false)]
theorem der_77554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77554 :=
  CNF.rup_sound cl_77554 [cl_74094,cl_77354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74094 v h) (hints_cons _ _ _ (der_77354 v h) (by intro d hd; cases hd)))
def cl_77556 : CNF.NClause := [(73,true),(131,true),(152,false),(18,true)]
theorem der_77556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77556 :=
  CNF.rup_sound cl_77556 [cl_76419,cl_62171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76419 v h) (hints_cons _ _ _ (der_62171 v h) (by intro d hd; cases hd)))
def cl_77560 : CNF.NClause := [(46,false),(15,true),(78,false),(81,false),(79,false)]
theorem der_77560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77560 :=
  CNF.rup_sound cl_77560 [cl_35626,cl_52039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35626 v h) (hints_cons _ _ _ (der_52039 v h) (by intro d hd; cases hd)))
def cl_77561 : CNF.NClause := [(49,false),(65,false),(18,true),(73,false),(69,false)]
theorem der_77561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77561 :=
  CNF.rup_sound cl_77561 [cl_52105,cl_59814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52105 v h) (hints_cons _ _ _ (der_59814 v h) (by intro d hd; cases hd)))
def cl_77563 : CNF.NClause := [(35,false),(63,true),(83,false),(73,false),(68,false)]
theorem der_77563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77563 :=
  CNF.rup_sound cl_77563 [cl_52109,cl_77163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52109 v h) (hints_cons _ _ _ (der_77163 v h) (by intro d hd; cases hd)))
def cl_77565 : CNF.NClause := [(46,false),(78,false),(79,false),(15,false),(77,true)]
theorem der_77565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77565 :=
  CNF.rup_sound cl_77565 [cl_32071,cl_50919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32071 v h) (hints_cons _ _ _ (der_50919 v h) (by intro d hd; cases hd)))
def cl_77567 : CNF.NClause := [(48,false),(76,true),(88,false),(70,false),(64,false)]
theorem der_77567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77567 :=
  CNF.rup_sound cl_77567 [cl_52116,cl_71388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52116 v h) (hints_cons _ _ _ (der_71388 v h) (by intro d hd; cases hd)))
def cl_77568 : CNF.NClause := [(48,false),(17,true),(64,false),(70,false),(83,true)]
theorem der_77568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77568 :=
  CNF.rup_sound cl_77568 [cl_32086,cl_51016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32086 v h) (hints_cons _ _ _ (der_51016 v h) (by intro d hd; cases hd)))
def cl_77571 : CNF.NClause := [(48,false),(76,true),(64,false),(17,true),(70,false)]
theorem der_77571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77571 :=
  CNF.rup_sound cl_77571 [cl_32089,cl_77567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32089 v h) (hints_cons _ _ _ (der_77567 v h) (by intro d hd; cases hd)))
def cl_77573 : CNF.NClause := [(39,false),(90,false),(79,false),(76,true),(82,false)]
theorem der_77573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77573 :=
  CNF.rup_sound cl_77573 [cl_52127,cl_77032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52127 v h) (hints_cons _ _ _ (der_77032 v h) (by intro d hd; cases hd)))
def cl_77574 : CNF.NClause := [(39,false),(79,false),(65,true),(82,false),(90,false)]
theorem der_77574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77574 :=
  CNF.rup_sound cl_77574 [cl_32109,cl_77032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32109 v h) (hints_cons _ _ _ (der_77032 v h) (by intro d hd; cases hd)))
def cl_77575 : CNF.NClause := [(39,false),(90,false),(8,true),(82,false),(79,false)]
theorem der_77575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77575 :=
  CNF.rup_sound cl_77575 [cl_32110,cl_50599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32110 v h) (hints_cons _ _ _ (der_50599 v h) (by intro d hd; cases hd)))
def cl_77578 : CNF.NClause := [(39,false),(82,false),(90,false),(76,false),(79,true)]
theorem der_77578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77578 :=
  CNF.rup_sound cl_77578 [cl_32113,cl_50602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32113 v h) (hints_cons _ _ _ (der_50602 v h) (by intro d hd; cases hd)))
def cl_77581 : CNF.NClause := [(39,false),(65,true),(90,false),(76,true),(82,false)]
theorem der_77581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77581 :=
  CNF.rup_sound cl_77581 [cl_32120,cl_77573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32120 v h) (hints_cons _ _ _ (der_77573 v h) (by intro d hd; cases hd)))
def cl_77582 : CNF.NClause := [(82,true),(39,false),(68,false),(65,false),(76,false)]
theorem der_77582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77582 :=
  CNF.rup_sound cl_77582 [cl_52134,cl_60238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52134 v h) (hints_cons _ _ _ (der_60238 v h) (by intro d hd; cases hd)))
def cl_77583 : CNF.NClause := [(39,false),(82,true),(79,false),(90,false),(76,false)]
theorem der_77583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77583 :=
  CNF.rup_sound cl_77583 [cl_52136,cl_52067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52136 v h) (hints_cons _ _ _ (der_52067 v h) (by intro d hd; cases hd)))
def cl_77585 : CNF.NClause := [(39,false),(79,false),(76,true),(90,false),(68,false)]
theorem der_77585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77585 :=
  CNF.rup_sound cl_77585 [cl_52137,cl_77032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52137 v h) (hints_cons _ _ _ (der_77032 v h) (by intro d hd; cases hd)))
def cl_77587 : CNF.NClause := [(39,false),(8,false),(76,true),(79,false),(90,false)]
theorem der_77587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77587 :=
  CNF.rup_sound cl_77587 [cl_32129,cl_77573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32129 v h) (hints_cons _ _ _ (der_77573 v h) (by intro d hd; cases hd)))
def cl_77594 : CNF.NClause := [(39,false),(82,true),(90,false),(65,false),(76,true)]
theorem der_77594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77594 :=
  CNF.rup_sound cl_77594 [cl_32139,cl_77036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32139 v h) (hints_cons _ _ _ (der_77036 v h) (by intro d hd; cases hd)))
def cl_77597 : CNF.NClause := [(39,false),(82,false),(90,true),(65,false),(79,false)]
theorem der_77597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77597 :=
  CNF.rup_sound cl_77597 [cl_32149,cl_56337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32149 v h) (hints_cons _ _ _ (der_56337 v h) (by intro d hd; cases hd)))
def cl_77598 : CNF.NClause := [(39,false),(8,true),(82,false),(76,true),(79,false)]
theorem der_77598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77598 :=
  CNF.rup_sound cl_77598 [cl_32152,cl_77511] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32152 v h) (hints_cons _ _ _ (der_77511 v h) (by intro d hd; cases hd)))
def cl_77601 : CNF.NClause := [(39,false),(65,true),(82,false),(68,false),(90,true)]
theorem der_77601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77601 :=
  CNF.rup_sound cl_77601 [cl_32155,cl_77511] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32155 v h) (hints_cons _ _ _ (der_77511 v h) (by intro d hd; cases hd)))
def cl_77603 : CNF.NClause := [(39,false),(76,false),(82,false),(8,true),(90,true)]
theorem der_77603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77603 :=
  CNF.rup_sound cl_77603 [cl_32159,cl_77033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32159 v h) (hints_cons _ _ _ (der_77033 v h) (by intro d hd; cases hd)))
def cl_77606 : CNF.NClause := [(39,false),(68,false),(82,false),(8,false),(90,true)]
theorem der_77606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77606 :=
  CNF.rup_sound cl_77606 [cl_32162,cl_50628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32162 v h) (hints_cons _ _ _ (der_50628 v h) (by intro d hd; cases hd)))
def cl_77610 : CNF.NClause := [(39,false),(82,true),(79,false),(76,false),(8,true)]
theorem der_77610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77610 :=
  CNF.rup_sound cl_77610 [cl_32173,cl_77583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32173 v h) (hints_cons _ _ _ (der_77583 v h) (by intro d hd; cases hd)))
def cl_77611 : CNF.NClause := [(39,false),(8,false),(65,false),(79,false),(90,true)]
theorem der_77611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77611 :=
  CNF.rup_sound cl_77611 [cl_32174,cl_77490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32174 v h) (hints_cons _ _ _ (der_77490 v h) (by intro d hd; cases hd)))
def cl_77612 : CNF.NClause := [(39,false),(82,true),(79,false),(8,true),(68,false)]
theorem der_77612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77612 :=
  CNF.rup_sound cl_77612 [cl_32177,cl_52067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32177 v h) (hints_cons _ _ _ (der_52067 v h) (by intro d hd; cases hd)))
def cl_77614 : CNF.NClause := [(39,false),(90,true),(68,false),(79,true),(8,false)]
theorem der_77614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77614 :=
  CNF.rup_sound cl_77614 [cl_52147,cl_77606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52147 v h) (hints_cons _ _ _ (der_77606 v h) (by intro d hd; cases hd)))
def cl_77616 : CNF.NClause := [(39,false),(65,false),(90,true),(8,true),(68,true)]
theorem der_77616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77616 :=
  CNF.rup_sound cl_77616 [cl_32193,cl_77033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32193 v h) (hints_cons _ _ _ (der_77033 v h) (by intro d hd; cases hd)))
def cl_77618 : CNF.NClause := [(39,false),(68,true),(76,true),(8,true),(82,true)]
theorem der_77618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77618 :=
  CNF.rup_sound cl_77618 [cl_52149,cl_50623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52149 v h) (hints_cons _ _ _ (der_50623 v h) (by intro d hd; cases hd)))
def cl_77619 : CNF.NClause := [(37,false),(78,false),(70,false),(74,true),(82,false)]
theorem der_77619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77619 :=
  CNF.rup_sound cl_77619 [cl_52151,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52151 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def cl_77620 : CNF.NClause := [(37,false),(66,true),(91,false),(70,false),(78,false)]
theorem der_77620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77620 :=
  CNF.rup_sound cl_77620 [cl_32195,cl_77048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32195 v h) (hints_cons _ _ _ (der_77048 v h) (by intro d hd; cases hd)))
def cl_77621 : CNF.NClause := [(37,false),(91,false),(74,false),(66,false),(78,true)]
theorem der_77621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77621 :=
  CNF.rup_sound cl_77621 [cl_52153,cl_49711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52153 v h) (hints_cons _ _ _ (der_49711 v h) (by intro d hd; cases hd)))
def cl_77623 : CNF.NClause := [(37,false),(70,true),(74,false),(91,false),(82,false)]
theorem der_77623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77623 :=
  CNF.rup_sound cl_77623 [cl_52155,cl_49706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52155 v h) (hints_cons _ _ _ (der_49706 v h) (by intro d hd; cases hd)))
def cl_77625 : CNF.NClause := [(37,false),(82,false),(66,false),(91,false),(78,true)]
theorem der_77625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77625 :=
  CNF.rup_sound cl_77625 [cl_32202,cl_77044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32202 v h) (hints_cons _ _ _ (der_77044 v h) (by intro d hd; cases hd)))
def cl_77626 : CNF.NClause := [(37,false),(91,false),(74,false),(66,false),(70,true)]
theorem der_77626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77626 :=
  CNF.rup_sound cl_77626 [cl_32211,cl_77621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32211 v h) (hints_cons _ _ _ (der_77621 v h) (by intro d hd; cases hd)))
def cl_77627 : CNF.NClause := [(37,false),(6,false),(91,false),(78,false),(70,true)]
theorem der_77627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77627 :=
  CNF.rup_sound cl_77627 [cl_32217,cl_50640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32217 v h) (hints_cons _ _ _ (der_50640 v h) (by intro d hd; cases hd)))
def cl_77628 : CNF.NClause := [(37,false),(82,true),(70,false),(91,false),(6,false)]
theorem der_77628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77628 :=
  CNF.rup_sound cl_77628 [cl_32226,cl_77043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32226 v h) (hints_cons _ _ _ (der_77043 v h) (by intro d hd; cases hd)))
def cl_77629 : CNF.NClause := [(37,false),(91,false),(66,false),(78,true),(70,false)]
theorem der_77629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77629 :=
  CNF.rup_sound cl_77629 [cl_32227,cl_77621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32227 v h) (hints_cons _ _ _ (der_77621 v h) (by intro d hd; cases hd)))
def cl_77631 : CNF.NClause := [(37,false),(91,true),(70,false),(82,false),(6,false)]
theorem der_77631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77631 :=
  CNF.rup_sound cl_77631 [cl_52158,cl_50656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52158 v h) (hints_cons _ _ _ (der_50656 v h) (by intro d hd; cases hd)))
def cl_77632 : CNF.NClause := [(37,false),(66,true),(82,false),(70,false),(78,false)]
theorem der_77632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77632 :=
  CNF.rup_sound cl_77632 [cl_52159,cl_77619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52159 v h) (hints_cons _ _ _ (der_77619 v h) (by intro d hd; cases hd)))
def cl_77633 : CNF.NClause := [(37,false),(74,true),(66,false),(82,false),(70,false)]
theorem der_77633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77633 :=
  CNF.rup_sound cl_77633 [cl_52160,cl_50550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52160 v h) (hints_cons _ _ _ (der_50550 v h) (by intro d hd; cases hd)))
def cl_77635 : CNF.NClause := [(37,false),(78,true),(6,false),(66,false),(82,false)]
theorem der_77635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77635 :=
  CNF.rup_sound cl_77635 [cl_52163,cl_77625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52163 v h) (hints_cons _ _ _ (der_77625 v h) (by intro d hd; cases hd)))
def cl_77636 : CNF.NClause := [(37,false),(70,true),(6,true),(82,false),(74,false)]
theorem der_77636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77636 :=
  CNF.rup_sound cl_77636 [cl_52164,cl_77623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52164 v h) (hints_cons _ _ _ (der_77623 v h) (by intro d hd; cases hd)))
def cl_77637 : CNF.NClause := [(37,false),(70,true),(78,false),(74,false),(6,false)]
theorem der_77637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77637 :=
  CNF.rup_sound cl_77637 [cl_32261,cl_77627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32261 v h) (hints_cons _ _ _ (der_77627 v h) (by intro d hd; cases hd)))
def cl_77639 : CNF.NClause := [(37,false),(82,true),(74,false),(6,false),(70,false)]
theorem der_77639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77639 :=
  CNF.rup_sound cl_77639 [cl_32271,cl_77047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32271 v h) (hints_cons _ _ _ (der_77047 v h) (by intro d hd; cases hd)))
def cl_77640 : CNF.NClause := [(37,false),(82,true),(78,true),(66,false),(70,false)]
theorem der_77640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77640 :=
  CNF.rup_sound cl_77640 [cl_52166,cl_77629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52166 v h) (hints_cons _ _ _ (der_77629 v h) (by intro d hd; cases hd)))
def cl_77641 : CNF.NClause := [(70,true),(37,false),(6,true),(66,false),(74,false)]
theorem der_77641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77641 :=
  CNF.rup_sound cl_77641 [cl_52167,cl_50661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52167 v h) (hints_cons _ _ _ (der_50661 v h) (by intro d hd; cases hd)))
def cl_77643 : CNF.NClause := [(37,false),(82,true),(91,true),(66,true),(74,false)]
theorem der_77643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77643 :=
  CNF.rup_sound cl_77643 [cl_32276,cl_77048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32276 v h) (hints_cons _ _ _ (der_77048 v h) (by intro d hd; cases hd)))
def cl_77644 : CNF.NClause := [(36,false),(92,false),(82,true),(86,false),(83,false)]
theorem der_77644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77644 :=
  CNF.rup_sound cl_77644 [cl_46029,cl_50679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46029 v h) (hints_cons _ _ _ (der_50679 v h) (by intro d hd; cases hd)))
def cl_77645 : CNF.NClause := [(36,false),(92,false),(83,true),(5,false),(84,false)]
theorem der_77645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77645 :=
  CNF.rup_sound cl_77645 [cl_52171,cl_50700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52171 v h) (hints_cons _ _ _ (der_50700 v h) (by intro d hd; cases hd)))
def cl_77646 : CNF.NClause := [(36,false),(86,false),(83,false),(84,true),(85,false)]
theorem der_77646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77646 :=
  CNF.rup_sound cl_77646 [cl_52172,cl_63482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52172 v h) (hints_cons _ _ _ (der_63482 v h) (by intro d hd; cases hd)))
def cl_77649 : CNF.NClause := [(36,false),(5,true),(92,false),(86,false),(83,false)]
theorem der_77649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77649 :=
  CNF.rup_sound cl_77649 [cl_32292,cl_77644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32292 v h) (hints_cons _ _ _ (der_77644 v h) (by intro d hd; cases hd)))
def cl_77650 : CNF.NClause := [(36,false),(92,false),(83,true),(84,false),(82,false)]
theorem der_77650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77650 :=
  CNF.rup_sound cl_77650 [cl_52177,cl_50682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52177 v h) (hints_cons _ _ _ (der_50682 v h) (by intro d hd; cases hd)))
def cl_77651 : CNF.NClause := [(36,false),(5,true),(92,false),(82,true),(85,false)]
theorem der_77651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77651 :=
  CNF.rup_sound cl_77651 [cl_32299,cl_52061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32299 v h) (hints_cons _ _ _ (der_52061 v h) (by intro d hd; cases hd)))
def cl_77652 : CNF.NClause := [(36,false),(86,true),(85,false),(92,false),(82,false)]
theorem der_77652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77652 :=
  CNF.rup_sound cl_77652 [cl_52178,cl_77051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52178 v h) (hints_cons _ _ _ (der_77051 v h) (by intro d hd; cases hd)))
def cl_77655 : CNF.NClause := [(36,false),(5,true),(92,false),(82,false),(84,false)]
theorem der_77655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77655 :=
  CNF.rup_sound cl_77655 [cl_32305,cl_50699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32305 v h) (hints_cons _ _ _ (der_50699 v h) (by intro d hd; cases hd)))
def cl_77656 : CNF.NClause := [(36,false),(5,false),(85,true),(92,false),(84,false)]
theorem der_77656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77656 :=
  CNF.rup_sound cl_77656 [cl_52181,cl_77645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52181 v h) (hints_cons _ _ _ (der_77645 v h) (by intro d hd; cases hd)))
def cl_77657 : CNF.NClause := [(36,false),(82,false),(85,true),(92,false),(84,false)]
theorem der_77657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77657 :=
  CNF.rup_sound cl_77657 [cl_32307,cl_77655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32307 v h) (hints_cons _ _ _ (der_77655 v h) (by intro d hd; cases hd)))
def cl_77659 : CNF.NClause := [(86,true),(92,false),(85,true),(36,false),(82,false)]
theorem der_77659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77659 :=
  CNF.rup_sound cl_77659 [cl_52182,cl_77657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52182 v h) (hints_cons _ _ _ (der_77657 v h) (by intro d hd; cases hd)))
def cl_77660 : CNF.NClause := [(82,true),(92,false),(84,true),(83,false),(36,false)]
theorem der_77660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77660 :=
  CNF.rup_sound cl_77660 [cl_32313,cl_77644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32313 v h) (hints_cons _ _ _ (der_77644 v h) (by intro d hd; cases hd)))
def cl_77661 : CNF.NClause := [(36,false),(92,false),(82,false),(86,true),(83,true)]
theorem der_77661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77661 :=
  CNF.rup_sound cl_77661 [cl_32315,cl_77650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32315 v h) (hints_cons _ _ _ (der_77650 v h) (by intro d hd; cases hd)))
def cl_77662 : CNF.NClause := [(36,false),(92,true),(86,false),(85,false),(83,false)]
theorem der_77662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77662 :=
  CNF.rup_sound cl_77662 [cl_52184,cl_77646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52184 v h) (hints_cons _ _ _ (der_77646 v h) (by intro d hd; cases hd)))
def cl_77663 : CNF.NClause := [(36,false),(82,true),(83,true),(5,false),(84,false)]
theorem der_77663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77663 :=
  CNF.rup_sound cl_77663 [cl_52186,cl_50700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52186 v h) (hints_cons _ _ _ (der_50700 v h) (by intro d hd; cases hd)))
def cl_77664 : CNF.NClause := [(36,false),(84,true),(85,false),(82,false),(83,true)]
theorem der_77664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77664 :=
  CNF.rup_sound cl_77664 [cl_52189,cl_77051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52189 v h) (hints_cons _ _ _ (der_77051 v h) (by intro d hd; cases hd)))
def cl_77665 : CNF.NClause := [(36,false),(82,true),(85,true),(84,false),(86,false)]
theorem der_77665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77665 :=
  CNF.rup_sound cl_77665 [cl_52191,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52191 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_77667 : CNF.NClause := [(36,false),(92,true),(86,false),(83,false),(84,true)]
theorem der_77667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77667 :=
  CNF.rup_sound cl_77667 [cl_32329,cl_77646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32329 v h) (hints_cons _ _ _ (der_77646 v h) (by intro d hd; cases hd)))
def cl_77668 : CNF.NClause := [(36,false),(82,true),(86,false),(83,true),(5,false)]
theorem der_77668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77668 :=
  CNF.rup_sound cl_77668 [cl_32332,cl_77663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32332 v h) (hints_cons _ _ _ (der_77663 v h) (by intro d hd; cases hd)))
def cl_77669 : CNF.NClause := [(36,false),(86,true),(85,false),(84,false),(5,false)]
theorem der_77669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77669 :=
  CNF.rup_sound cl_77669 [cl_52195,cl_50696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52195 v h) (hints_cons _ _ _ (der_50696 v h) (by intro d hd; cases hd)))
def cl_77670 : CNF.NClause := [(36,false),(85,false),(83,false),(84,true),(82,false)]
theorem der_77670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77670 :=
  CNF.rup_sound cl_77670 [cl_52197,cl_77646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52197 v h) (hints_cons _ _ _ (der_77646 v h) (by intro d hd; cases hd)))
def cl_77671 : CNF.NClause := [(36,false),(84,true),(85,false),(5,false),(83,false)]
theorem der_77671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77671 :=
  CNF.rup_sound cl_77671 [cl_32340,cl_77670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32340 v h) (hints_cons _ _ _ (der_77670 v h) (by intro d hd; cases hd)))
def cl_77673 : CNF.NClause := [(36,false),(86,true),(5,false),(82,false),(84,false)]
theorem der_77673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77673 :=
  CNF.rup_sound cl_77673 [cl_32346,cl_50700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32346 v h) (hints_cons _ _ _ (der_50700 v h) (by intro d hd; cases hd)))
def cl_77674 : CNF.NClause := [(36,false),(83,false),(82,false),(85,true),(84,false)]
theorem der_77674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77674 :=
  CNF.rup_sound cl_77674 [cl_52198,cl_77657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52198 v h) (hints_cons _ _ _ (der_77657 v h) (by intro d hd; cases hd)))
def cl_77675 : CNF.NClause := [(36,false),(92,true),(86,true),(84,false),(5,false)]
theorem der_77675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77675 :=
  CNF.rup_sound cl_77675 [cl_32347,cl_50700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32347 v h) (hints_cons _ _ _ (der_50700 v h) (by intro d hd; cases hd)))
def cl_77676 : CNF.NClause := [(36,false),(84,false),(85,true),(83,true),(82,false)]
theorem der_77676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77676 :=
  CNF.rup_sound cl_77676 [cl_32349,cl_50699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32349 v h) (hints_cons _ _ _ (der_50699 v h) (by intro d hd; cases hd)))
def cl_77677 : CNF.NClause := [(36,false),(5,false),(84,true),(82,false),(83,false)]
theorem der_77677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77677 :=
  CNF.rup_sound cl_77677 [cl_32353,cl_77671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32353 v h) (hints_cons _ _ _ (der_77671 v h) (by intro d hd; cases hd)))
def cl_77678 : CNF.NClause := [(36,false),(92,true),(84,true),(83,false),(82,false)]
theorem der_77678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77678 :=
  CNF.rup_sound cl_77678 [cl_32354,cl_77677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32354 v h) (hints_cons _ _ _ (der_77677 v h) (by intro d hd; cases hd)))
def cl_77680 : CNF.NClause := [(36,false),(84,true),(85,true),(92,true),(83,false)]
theorem der_77680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77680 :=
  CNF.rup_sound cl_77680 [cl_32356,cl_77678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32356 v h) (hints_cons _ _ _ (der_77678 v h) (by intro d hd; cases hd)))
def cl_77682 : CNF.NClause := [(49,false),(65,false),(77,true),(69,false),(73,false)]
theorem der_77682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77682 :=
  CNF.rup_sound cl_77682 [cl_52201,cl_59814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52201 v h) (hints_cons _ _ _ (der_59814 v h) (by intro d hd; cases hd)))
def cl_77683 : CNF.NClause := [(57,false),(62,true),(91,false),(26,true),(75,false)]
theorem der_77683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77683 :=
  CNF.rup_sound cl_77683 [cl_32372,cl_77168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32372 v h) (hints_cons _ _ _ (der_77168 v h) (by intro d hd; cases hd)))
def cl_77693 : CNF.NClause := [(40,false),(63,false),(69,false),(81,false),(9,true)]
theorem der_77693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77693 :=
  CNF.rup_sound cl_77693 [cl_32430,cl_77457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32430 v h) (hints_cons _ _ _ (der_77457 v h) (by intro d hd; cases hd)))
def cl_77694 : CNF.NClause := [(40,false),(82,true),(69,true),(63,false),(9,true)]
theorem der_77694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77694 :=
  CNF.rup_sound cl_77694 [cl_32435,cl_77457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32435 v h) (hints_cons _ _ _ (der_77457 v h) (by intro d hd; cases hd)))
def cl_77696 : CNF.NClause := [(58,false),(89,false),(76,true),(69,false),(78,false)]
theorem der_77696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77696 :=
  CNF.rup_sound cl_77696 [cl_52218,cl_62008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52218 v h) (hints_cons _ _ _ (der_62008 v h) (by intro d hd; cases hd)))
def cl_77697 : CNF.NClause := [(58,false),(62,true),(78,false),(85,false),(89,false)]
theorem der_77697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77697 :=
  CNF.rup_sound cl_77697 [cl_32450,cl_50743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32450 v h) (hints_cons _ _ _ (der_50743 v h) (by intro d hd; cases hd)))
def cl_77698 : CNF.NClause := [(58,false),(27,false),(69,true),(85,false),(78,false)]
theorem der_77698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77698 :=
  CNF.rup_sound cl_77698 [cl_52219,cl_50750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52219 v h) (hints_cons _ _ _ (der_50750 v h) (by intro d hd; cases hd)))
def cl_77700 : CNF.NClause := [(58,false),(85,false),(89,false),(76,false),(78,true)]
theorem der_77700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77700 :=
  CNF.rup_sound cl_77700 [cl_32456,cl_54044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32456 v h) (hints_cons _ _ _ (der_54044 v h) (by intro d hd; cases hd)))
def cl_77701 : CNF.NClause := [(58,false),(89,false),(76,true),(69,false),(85,false)]
theorem der_77701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77701 :=
  CNF.rup_sound cl_77701 [cl_52220,cl_77058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52220 v h) (hints_cons _ _ _ (der_77058 v h) (by intro d hd; cases hd)))
def cl_77702 : CNF.NClause := [(58,false),(85,false),(62,false),(78,true),(89,false)]
theorem der_77702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77702 :=
  CNF.rup_sound cl_77702 [cl_32460,cl_77058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32460 v h) (hints_cons _ _ _ (der_77058 v h) (by intro d hd; cases hd)))
def cl_77705 : CNF.NClause := [(58,false),(62,true),(27,true),(78,false),(89,false)]
theorem der_77705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77705 :=
  CNF.rup_sound cl_77705 [cl_52224,cl_50743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52224 v h) (hints_cons _ _ _ (der_50743 v h) (by intro d hd; cases hd)))
def cl_77707 : CNF.NClause := [(58,false),(27,false),(89,false),(85,true),(62,false)]
theorem der_77707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77707 :=
  CNF.rup_sound cl_77707 [cl_52225,cl_77059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52225 v h) (hints_cons _ _ _ (der_77059 v h) (by intro d hd; cases hd)))
def cl_77708 : CNF.NClause := [(58,false),(27,true),(69,true),(78,false),(89,false)]
theorem der_77708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77708 :=
  CNF.rup_sound cl_77708 [cl_32470,cl_50761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32470 v h) (hints_cons _ _ _ (der_50761 v h) (by intro d hd; cases hd)))
def cl_77711 : CNF.NClause := [(58,false),(89,false),(69,false),(78,true),(76,false)]
theorem der_77711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77711 :=
  CNF.rup_sound cl_77711 [cl_52228,cl_54044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52228 v h) (hints_cons _ _ _ (der_54044 v h) (by intro d hd; cases hd)))
def cl_77712 : CNF.NClause := [(58,false),(62,true),(78,true),(89,false),(76,false)]
theorem der_77712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77712 :=
  CNF.rup_sound cl_77712 [cl_52229,cl_77700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52229 v h) (hints_cons _ _ _ (der_77700 v h) (by intro d hd; cases hd)))
def cl_77715 : CNF.NClause := [(58,false),(78,true),(89,false),(85,true),(69,false)]
theorem der_77715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77715 :=
  CNF.rup_sound cl_77715 [cl_32479,cl_62008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32479 v h) (hints_cons _ _ _ (der_62008 v h) (by intro d hd; cases hd)))
def cl_77718 : CNF.NClause := [(27,true),(85,true),(89,false),(58,false),(78,true)]
theorem der_77718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77718 :=
  CNF.rup_sound cl_77718 [cl_32484,cl_54044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32484 v h) (hints_cons _ _ _ (der_54044 v h) (by intro d hd; cases hd)))
def cl_77721 : CNF.NClause := [(58,false),(62,true),(78,true),(69,false),(76,false)]
theorem der_77721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77721 :=
  CNF.rup_sound cl_77721 [cl_52235,cl_77711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52235 v h) (hints_cons _ _ _ (der_77711 v h) (by intro d hd; cases hd)))
def cl_77722 : CNF.NClause := [(58,false),(62,false),(85,false),(69,true),(76,false)]
theorem der_77722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77722 :=
  CNF.rup_sound cl_77722 [cl_52236,cl_52089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52236 v h) (hints_cons _ _ _ (der_52089 v h) (by intro d hd; cases hd)))
def cl_77723 : CNF.NClause := [(58,false),(27,false),(89,true),(85,false),(76,false)]
theorem der_77723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77723 :=
  CNF.rup_sound cl_77723 [cl_32498,cl_52232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32498 v h) (hints_cons _ _ _ (der_52232 v h) (by intro d hd; cases hd)))
def cl_77725 : CNF.NClause := [(58,false),(27,true),(78,true),(76,true),(85,false)]
theorem der_77725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77725 :=
  CNF.rup_sound cl_77725 [cl_52237,cl_77058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52237 v h) (hints_cons _ _ _ (der_77058 v h) (by intro d hd; cases hd)))
def cl_77726 : CNF.NClause := [(58,false),(62,false),(85,true),(69,false),(78,false)]
theorem der_77726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77726 :=
  CNF.rup_sound cl_77726 [cl_52238,cl_77061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52238 v h) (hints_cons _ _ _ (der_77061 v h) (by intro d hd; cases hd)))
def cl_77728 : CNF.NClause := [(27,false),(58,false),(78,false),(76,false),(85,true)]
theorem der_77728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77728 :=
  CNF.rup_sound cl_77728 [cl_32507,cl_50755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32507 v h) (hints_cons _ _ _ (der_50755 v h) (by intro d hd; cases hd)))
def cl_77729 : CNF.NClause := [(58,false),(62,true),(76,false),(27,true),(78,false)]
theorem der_77729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77729 :=
  CNF.rup_sound cl_77729 [cl_32508,cl_50756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32508 v h) (hints_cons _ _ _ (der_50756 v h) (by intro d hd; cases hd)))
def cl_77730 : CNF.NClause := [(58,false),(62,false),(69,true),(78,false),(76,false)]
theorem der_77730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77730 :=
  CNF.rup_sound cl_77730 [cl_32510,cl_52089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32510 v h) (hints_cons _ _ _ (der_52089 v h) (by intro d hd; cases hd)))
def cl_77731 : CNF.NClause := [(58,false),(69,false),(78,false),(76,true),(62,false)]
theorem der_77731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77731 :=
  CNF.rup_sound cl_77731 [cl_32513,cl_77061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32513 v h) (hints_cons _ _ _ (der_77061 v h) (by intro d hd; cases hd)))
def cl_77732 : CNF.NClause := [(58,false),(27,false),(76,false),(78,true),(69,false)]
theorem der_77732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77732 :=
  CNF.rup_sound cl_77732 [cl_32521,cl_77721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32521 v h) (hints_cons _ _ _ (der_77721 v h) (by intro d hd; cases hd)))
def cl_77734 : CNF.NClause := [(58,false),(62,true),(76,false),(69,true),(27,true)]
theorem der_77734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77734 :=
  CNF.rup_sound cl_77734 [cl_32528,cl_54044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32528 v h) (hints_cons _ _ _ (der_54044 v h) (by intro d hd; cases hd)))
def cl_77735 : CNF.NClause := [(62,false),(85,true),(27,true),(58,false),(78,true)]
theorem der_77735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77735 :=
  CNF.rup_sound cl_77735 [cl_32533,cl_77061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32533 v h) (hints_cons _ _ _ (der_77061 v h) (by intro d hd; cases hd)))
def cl_77736 : CNF.NClause := [(54,false),(65,true),(89,false),(74,false),(23,false)]
theorem der_77736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77736 :=
  CNF.rup_sound cl_77736 [cl_52240,cl_77064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52240 v h) (hints_cons _ _ _ (der_77064 v h) (by intro d hd; cases hd)))
def cl_77737 : CNF.NClause := [(54,false),(67,true),(74,false),(23,false),(89,false)]
theorem der_77737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77737 :=
  CNF.rup_sound cl_77737 [cl_52242,cl_77736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52242 v h) (hints_cons _ _ _ (der_77736 v h) (by intro d hd; cases hd)))
def cl_77738 : CNF.NClause := [(54,false),(65,true),(23,false),(83,false),(89,false)]
theorem der_77738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77738 :=
  CNF.rup_sound cl_77738 [cl_52244,cl_77064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52244 v h) (hints_cons _ _ _ (der_77064 v h) (by intro d hd; cases hd)))
def cl_77739 : CNF.NClause := [(54,false),(65,true),(89,false),(83,false),(81,false)]
theorem der_77739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77739 :=
  CNF.rup_sound cl_77739 [cl_32537,cl_77066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32537 v h) (hints_cons _ _ _ (der_77066 v h) (by intro d hd; cases hd)))
def cl_77740 : CNF.NClause := [(54,false),(23,true),(89,false),(83,false),(81,false)]
theorem der_77740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77740 :=
  CNF.rup_sound cl_77740 [cl_32538,cl_77739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32538 v h) (hints_cons _ _ _ (der_77739 v h) (by intro d hd; cases hd)))
def cl_77741 : CNF.NClause := [(54,false),(81,true),(89,false),(67,false),(23,false)]
theorem der_77741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77741 :=
  CNF.rup_sound cl_77741 [cl_52246,cl_56354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52246 v h) (hints_cons _ _ _ (der_56354 v h) (by intro d hd; cases hd)))
def cl_77743 : CNF.NClause := [(54,false),(23,false),(89,false),(83,false),(74,true)]
theorem der_77743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77743 :=
  CNF.rup_sound cl_77743 [cl_32548,cl_77738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32548 v h) (hints_cons _ _ _ (der_77738 v h) (by intro d hd; cases hd)))
def cl_77744 : CNF.NClause := [(54,false),(65,true),(74,true),(83,false),(67,true)]
theorem der_77744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77744 :=
  CNF.rup_sound cl_77744 [cl_32551,cl_50789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32551 v h) (hints_cons _ _ _ (der_50789 v h) (by intro d hd; cases hd)))
def cl_77745 : CNF.NClause := [(54,false),(23,true),(81,false),(65,false),(74,false)]
theorem der_77745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77745 :=
  CNF.rup_sound cl_77745 [cl_52249,cl_50802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52249 v h) (hints_cons _ _ _ (der_50802 v h) (by intro d hd; cases hd)))
def cl_77746 : CNF.NClause := [(54,false),(65,true),(81,false),(74,false),(89,false)]
theorem der_77746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77746 :=
  CNF.rup_sound cl_77746 [cl_32552,cl_77066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32552 v h) (hints_cons _ _ _ (der_77066 v h) (by intro d hd; cases hd)))
def cl_77748 : CNF.NClause := [(54,false),(74,false),(67,true),(89,false),(81,false)]
theorem der_77748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77748 :=
  CNF.rup_sound cl_77748 [cl_32553,cl_77066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32553 v h) (hints_cons _ _ _ (der_77066 v h) (by intro d hd; cases hd)))
def cl_77749 : CNF.NClause := [(54,false),(83,true),(67,false),(89,false),(81,false)]
theorem der_77749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77749 :=
  CNF.rup_sound cl_77749 [cl_32557,cl_52091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32557 v h) (hints_cons _ _ _ (der_52091 v h) (by intro d hd; cases hd)))
def cl_77750 : CNF.NClause := [(54,false),(23,true),(89,false),(65,false),(81,false)]
theorem der_77750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77750 :=
  CNF.rup_sound cl_77750 [cl_32558,cl_77745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32558 v h) (hints_cons _ _ _ (der_77745 v h) (by intro d hd; cases hd)))
def cl_77751 : CNF.NClause := [(54,false),(65,true),(89,false),(23,false),(67,true)]
theorem der_77751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77751 :=
  CNF.rup_sound cl_77751 [cl_32559,cl_77064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32559 v h) (hints_cons _ _ _ (der_77064 v h) (by intro d hd; cases hd)))
def cl_77753 : CNF.NClause := [(54,false),(23,false),(83,true),(74,false),(89,false)]
theorem der_77753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77753 :=
  CNF.rup_sound cl_77753 [cl_32564,cl_77736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32564 v h) (hints_cons _ _ _ (der_77736 v h) (by intro d hd; cases hd)))
def cl_77754 : CNF.NClause := [(54,false),(65,true),(83,true),(81,true),(67,false)]
theorem der_77754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77754 :=
  CNF.rup_sound cl_77754 [cl_52253,cl_77064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52253 v h) (hints_cons _ _ _ (der_77064 v h) (by intro d hd; cases hd)))
def cl_77756 : CNF.NClause := [(54,false),(65,true),(89,false),(67,true),(83,true)]
theorem der_77756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77756 :=
  CNF.rup_sound cl_77756 [cl_32574,cl_77751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32574 v h) (hints_cons _ _ _ (der_77751 v h) (by intro d hd; cases hd)))
def cl_77759 : CNF.NClause := [(54,false),(23,false),(67,false),(81,false),(74,true)]
theorem der_77759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77759 :=
  CNF.rup_sound cl_77759 [cl_32579,cl_57003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32579 v h) (hints_cons _ _ _ (der_57003 v h) (by intro d hd; cases hd)))
def cl_77760 : CNF.NClause := [(54,false),(74,true),(89,true),(67,false),(83,false)]
theorem der_77760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77760 :=
  CNF.rup_sound cl_77760 [cl_32580,cl_50787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32580 v h) (hints_cons _ _ _ (der_50787 v h) (by intro d hd; cases hd)))
def cl_77762 : CNF.NClause := [(54,false),(23,true),(83,false),(81,false),(67,true)]
theorem der_77762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77762 :=
  CNF.rup_sound cl_77762 [cl_32582,cl_50783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32582 v h) (hints_cons _ _ _ (der_50783 v h) (by intro d hd; cases hd)))
def cl_77763 : CNF.NClause := [(54,false),(81,true),(67,false),(23,false),(83,false)]
theorem der_77763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77763 :=
  CNF.rup_sound cl_77763 [cl_52257,cl_50787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52257 v h) (hints_cons _ _ _ (der_50787 v h) (by intro d hd; cases hd)))
def cl_77764 : CNF.NClause := [(54,false),(81,true),(83,false),(67,false),(74,false)]
theorem der_77764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77764 :=
  CNF.rup_sound cl_77764 [cl_32587,cl_77763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32587 v h) (hints_cons _ _ _ (der_77763 v h) (by intro d hd; cases hd)))
def cl_77765 : CNF.NClause := [(54,false),(81,true),(23,false),(74,false),(65,false)]
theorem der_77765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77765 :=
  CNF.rup_sound cl_77765 [cl_32588,cl_56354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32588 v h) (hints_cons _ _ _ (der_56354 v h) (by intro d hd; cases hd)))
def cl_77768 : CNF.NClause := [(54,false),(89,true),(67,true),(23,false),(83,false)]
theorem der_77768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77768 :=
  CNF.rup_sound cl_77768 [cl_52258,cl_77065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52258 v h) (hints_cons _ _ _ (der_77065 v h) (by intro d hd; cases hd)))
def cl_77769 : CNF.NClause := [(54,false),(74,false),(89,true),(65,false),(81,false)]
theorem der_77769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77769 :=
  CNF.rup_sound cl_77769 [cl_52259,cl_50802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52259 v h) (hints_cons _ _ _ (der_50802 v h) (by intro d hd; cases hd)))
def cl_77770 : CNF.NClause := [(54,false),(65,true),(67,false),(74,false),(23,false)]
theorem der_77770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77770 :=
  CNF.rup_sound cl_77770 [cl_32600,cl_77064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32600 v h) (hints_cons _ _ _ (der_77064 v h) (by intro d hd; cases hd)))
def cl_77772 : CNF.NClause := [(54,false),(83,true),(23,true),(89,true),(81,false)]
theorem der_77772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77772 :=
  CNF.rup_sound cl_77772 [cl_52260,cl_50796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52260 v h) (hints_cons _ _ _ (der_50796 v h) (by intro d hd; cases hd)))
def cl_77773 : CNF.NClause := [(54,false),(65,false),(83,true),(67,false),(74,false)]
theorem der_77773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77773 :=
  CNF.rup_sound cl_77773 [cl_32613,cl_50799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32613 v h) (hints_cons _ _ _ (der_50799 v h) (by intro d hd; cases hd)))
def cl_77776 : CNF.NClause := [(40,false),(63,true),(82,false),(9,false),(69,false)]
theorem der_77776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77776 :=
  CNF.rup_sound cl_77776 [cl_52261,cl_77074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52261 v h) (hints_cons _ _ _ (der_77074 v h) (by intro d hd; cases hd)))
def cl_77777 : CNF.NClause := [(63,true),(40,false),(75,false),(81,false),(88,false)]
theorem der_77777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77777 :=
  CNF.rup_sound cl_77777 [cl_42663,cl_77078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42663 v h) (hints_cons _ _ _ (der_77078 v h) (by intro d hd; cases hd)))
def cl_77778 : CNF.NClause := [(40,false),(63,true),(81,false),(88,false),(82,false)]
theorem der_77778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77778 :=
  CNF.rup_sound cl_77778 [cl_32640,cl_50823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32640 v h) (hints_cons _ _ _ (der_50823 v h) (by intro d hd; cases hd)))
def cl_77780 : CNF.NClause := [(40,false),(75,true),(88,false),(81,false),(82,false)]
theorem der_77780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77780 :=
  CNF.rup_sound cl_77780 [cl_32642,cl_77778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32642 v h) (hints_cons _ _ _ (der_77778 v h) (by intro d hd; cases hd)))
def cl_77782 : CNF.NClause := [(40,false),(81,true),(63,false),(88,false),(82,false)]
theorem der_77782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77782 :=
  CNF.rup_sound cl_77782 [cl_32646,cl_77077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32646 v h) (hints_cons _ _ _ (der_77077 v h) (by intro d hd; cases hd)))
def cl_77786 : CNF.NClause := [(40,false),(82,true),(81,false),(63,false),(88,false)]
theorem der_77786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77786 :=
  CNF.rup_sound cl_77786 [cl_52265,cl_50830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52265 v h) (hints_cons _ _ _ (der_50830 v h) (by intro d hd; cases hd)))
def cl_77787 : CNF.NClause := [(40,false),(82,true),(88,false),(81,false),(69,false)]
theorem der_77787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77787 :=
  CNF.rup_sound cl_77787 [cl_32655,cl_77073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32655 v h) (hints_cons _ _ _ (der_77073 v h) (by intro d hd; cases hd)))
def cl_77788 : CNF.NClause := [(40,false),(82,true),(9,false),(88,false),(81,false)]
theorem der_77788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77788 :=
  CNF.rup_sound cl_77788 [cl_32657,cl_77072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32657 v h) (hints_cons _ _ _ (der_77072 v h) (by intro d hd; cases hd)))
def cl_77790 : CNF.NClause := [(40,false),(81,true),(88,false),(75,false),(63,false)]
theorem der_77790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77790 :=
  CNF.rup_sound cl_77790 [cl_32664,cl_77081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32664 v h) (hints_cons _ _ _ (der_77081 v h) (by intro d hd; cases hd)))
def cl_77791 : CNF.NClause := [(40,false),(9,false),(69,false),(81,true),(88,false)]
theorem der_77791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77791 :=
  CNF.rup_sound cl_77791 [cl_32665,cl_77072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32665 v h) (hints_cons _ _ _ (der_77072 v h) (by intro d hd; cases hd)))
def cl_77792 : CNF.NClause := [(40,false),(63,true),(88,false),(69,true),(9,false)]
theorem der_77792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77792 :=
  CNF.rup_sound cl_77792 [cl_32668,cl_77072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32668 v h) (hints_cons _ _ _ (der_77072 v h) (by intro d hd; cases hd)))
def cl_77793 : CNF.NClause := [(40,false),(9,false),(63,true),(88,false),(69,false)]
theorem der_77793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77793 :=
  CNF.rup_sound cl_77793 [cl_52267,cl_77776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52267 v h) (hints_cons _ _ _ (der_77776 v h) (by intro d hd; cases hd)))
def cl_77794 : CNF.NClause := [(40,false),(88,true),(75,false),(82,false),(63,false)]
theorem der_77794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77794 :=
  CNF.rup_sound cl_77794 [cl_52268,cl_77075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52268 v h) (hints_cons _ _ _ (der_77075 v h) (by intro d hd; cases hd)))
def cl_77795 : CNF.NClause := [(40,false),(88,true),(82,false),(75,false),(69,false)]
theorem der_77795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77795 :=
  CNF.rup_sound cl_77795 [cl_52269,cl_77056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52269 v h) (hints_cons _ _ _ (der_77056 v h) (by intro d hd; cases hd)))
def cl_77796 : CNF.NClause := [(40,false),(88,true),(75,false),(81,false),(82,false)]
theorem der_77796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77796 :=
  CNF.rup_sound cl_77796 [cl_32676,cl_50842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32676 v h) (hints_cons _ _ _ (der_50842 v h) (by intro d hd; cases hd)))
def cl_77797 : CNF.NClause := [(40,false),(82,false),(75,false),(69,true),(81,false)]
theorem der_77797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77797 :=
  CNF.rup_sound cl_77797 [cl_32678,cl_77080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32678 v h) (hints_cons _ _ _ (der_77080 v h) (by intro d hd; cases hd)))
def cl_77798 : CNF.NClause := [(40,false),(75,true),(69,false),(63,false),(82,false)]
theorem der_77798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77798 :=
  CNF.rup_sound cl_77798 [cl_32680,cl_77077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32680 v h) (hints_cons _ _ _ (der_77077 v h) (by intro d hd; cases hd)))
def cl_77799 : CNF.NClause := [(40,false),(63,true),(82,false),(69,false),(81,false)]
theorem der_77799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77799 :=
  CNF.rup_sound cl_77799 [cl_52270,cl_77778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52270 v h) (hints_cons _ _ _ (der_77778 v h) (by intro d hd; cases hd)))
def cl_77805 : CNF.NClause := [(40,false),(82,true),(75,false),(63,false),(81,false)]
theorem der_77805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77805 :=
  CNF.rup_sound cl_77805 [cl_52271,cl_77457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52271 v h) (hints_cons _ _ _ (der_77457 v h) (by intro d hd; cases hd)))
def cl_77806 : CNF.NClause := [(40,false),(69,false),(9,false),(81,false),(82,true)]
theorem der_77806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77806 :=
  CNF.rup_sound cl_77806 [cl_52272,cl_77787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52272 v h) (hints_cons _ _ _ (der_77787 v h) (by intro d hd; cases hd)))
def cl_77807 : CNF.NClause := [(40,false),(63,true),(81,false),(9,false),(88,true)]
theorem der_77807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77807 :=
  CNF.rup_sound cl_77807 [cl_32703,cl_50855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32703 v h) (hints_cons _ _ _ (der_50855 v h) (by intro d hd; cases hd)))
def cl_77808 : CNF.NClause := [(40,false),(63,true),(81,false),(75,true),(69,false)]
theorem der_77808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77808 :=
  CNF.rup_sound cl_77808 [cl_32704,cl_77799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32704 v h) (hints_cons _ _ _ (der_77799 v h) (by intro d hd; cases hd)))
def cl_77809 : CNF.NClause := [(40,false),(9,false),(82,true),(63,false),(81,false)]
theorem der_77809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77809 :=
  CNF.rup_sound cl_77809 [cl_32705,cl_77788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32705 v h) (hints_cons _ _ _ (der_77788 v h) (by intro d hd; cases hd)))
def cl_77811 : CNF.NClause := [(40,false),(88,true),(75,false),(69,false),(63,false)]
theorem der_77811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77811 :=
  CNF.rup_sound cl_77811 [cl_52273,cl_77794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52273 v h) (hints_cons _ _ _ (der_77794 v h) (by intro d hd; cases hd)))
def cl_77817 : CNF.NClause := [(40,false),(82,true),(69,true),(88,true),(9,true)]
theorem der_77817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77817 :=
  CNF.rup_sound cl_77817 [cl_32715,cl_77694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32715 v h) (hints_cons _ _ _ (der_77694 v h) (by intro d hd; cases hd)))
def cl_77818 : CNF.NClause := [(60,false),(62,true),(74,false),(80,false),(88,false)]
theorem der_77818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77818 :=
  CNF.rup_sound cl_77818 [cl_52279,cl_62170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52279 v h) (hints_cons _ _ _ (der_62170 v h) (by intro d hd; cases hd)))
def cl_77819 : CNF.NClause := [(60,false),(62,true),(88,false),(68,false),(86,false)]
theorem der_77819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77819 :=
  CNF.rup_sound cl_77819 [cl_32719,cl_61896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32719 v h) (hints_cons _ _ _ (der_61896 v h) (by intro d hd; cases hd)))
def cl_77820 : CNF.NClause := [(60,false),(62,true),(86,false),(88,false),(80,false)]
theorem der_77820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77820 :=
  CNF.rup_sound cl_77820 [cl_32721,cl_61829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32721 v h) (hints_cons _ _ _ (der_61829 v h) (by intro d hd; cases hd)))
def cl_77822 : CNF.NClause := [(60,false),(68,false),(86,false),(88,false),(74,true)]
theorem der_77822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77822 :=
  CNF.rup_sound cl_77822 [cl_32725,cl_77819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32725 v h) (hints_cons _ _ _ (der_77819 v h) (by intro d hd; cases hd)))
def cl_77828 : CNF.NClause := [(60,false),(88,false),(80,false),(29,false),(68,true)]
theorem der_77828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77828 :=
  CNF.rup_sound cl_77828 [cl_32738,cl_52277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32738 v h) (hints_cons _ _ _ (der_52277 v h) (by intro d hd; cases hd)))
def cl_77829 : CNF.NClause := [(60,false),(68,true),(88,false),(86,true),(80,false)]
theorem der_77829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77829 :=
  CNF.rup_sound cl_77829 [cl_52290,cl_50865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52290 v h) (hints_cons _ _ _ (der_50865 v h) (by intro d hd; cases hd)))
def cl_77830 : CNF.NClause := [(60,false),(62,true),(74,false),(88,false),(68,false)]
theorem der_77830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77830 :=
  CNF.rup_sound cl_77830 [cl_32740,cl_50862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32740 v h) (hints_cons _ _ _ (der_50862 v h) (by intro d hd; cases hd)))
def cl_77831 : CNF.NClause := [(60,false),(88,false),(74,false),(86,true),(68,true)]
theorem der_77831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77831 :=
  CNF.rup_sound cl_77831 [cl_32745,cl_62170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32745 v h) (hints_cons _ _ _ (der_62170 v h) (by intro d hd; cases hd)))
def cl_77832 : CNF.NClause := [(62,true),(60,false),(68,false),(88,false),(74,true)]
theorem der_77832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77832 :=
  CNF.rup_sound cl_77832 [cl_32749,cl_77819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32749 v h) (hints_cons _ _ _ (der_77819 v h) (by intro d hd; cases hd)))
def cl_77833 : CNF.NClause := [(29,false),(88,false),(60,false),(86,true),(62,false)]
theorem der_77833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77833 :=
  CNF.rup_sound cl_77833 [cl_32750,cl_52291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32750 v h) (hints_cons _ _ _ (der_52291 v h) (by intro d hd; cases hd)))
def cl_77834 : CNF.NClause := [(62,true),(60,false),(29,true),(88,false),(74,true)]
theorem der_77834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77834 :=
  CNF.rup_sound cl_77834 [cl_32753,cl_77832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32753 v h) (hints_cons _ _ _ (der_77832 v h) (by intro d hd; cases hd)))
def cl_77836 : CNF.NClause := [(60,false),(62,false),(86,false),(74,true),(80,false)]
theorem der_77836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77836 :=
  CNF.rup_sound cl_77836 [cl_32761,cl_32757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32761 v h) (hints_cons _ _ _ (der_32757 v h) (by intro d hd; cases hd)))
def cl_77837 : CNF.NClause := [(60,false),(62,true),(86,false),(80,false),(74,true)]
theorem der_77837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77837 :=
  CNF.rup_sound cl_77837 [cl_32763,cl_77820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32763 v h) (hints_cons _ _ _ (der_77820 v h) (by intro d hd; cases hd)))
def cl_77838 : CNF.NClause := [(60,false),(62,false),(29,false),(74,false),(88,true)]
theorem der_77838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77838 :=
  CNF.rup_sound cl_77838 [cl_52295,cl_50866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52295 v h) (hints_cons _ _ _ (der_50866 v h) (by intro d hd; cases hd)))
def cl_77839 : CNF.NClause := [(60,false),(80,true),(68,true),(74,false),(62,false)]
theorem der_77839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77839 :=
  CNF.rup_sound cl_77839 [cl_32768,cl_50868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32768 v h) (hints_cons _ _ _ (der_50868 v h) (by intro d hd; cases hd)))
def cl_77840 : CNF.NClause := [(60,false),(74,false),(86,false),(29,false),(88,true)]
theorem der_77840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77840 :=
  CNF.rup_sound cl_77840 [cl_32769,cl_77838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32769 v h) (hints_cons _ _ _ (der_77838 v h) (by intro d hd; cases hd)))
def cl_77841 : CNF.NClause := [(60,false),(86,false),(74,true),(68,false),(62,false)]
theorem der_77841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77841 :=
  CNF.rup_sound cl_77841 [cl_32772,cl_32757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32772 v h) (hints_cons _ _ _ (der_32757 v h) (by intro d hd; cases hd)))
def cl_77843 : CNF.NClause := [(60,false),(80,true),(68,false),(86,false),(62,true)]
theorem der_77843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77843 :=
  CNF.rup_sound cl_77843 [cl_32774,cl_61896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32774 v h) (hints_cons _ _ _ (der_61896 v h) (by intro d hd; cases hd)))
def cl_77844 : CNF.NClause := [(60,false),(29,false),(62,false),(88,true),(86,false)]
theorem der_77844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77844 :=
  CNF.rup_sound cl_77844 [cl_32775,cl_77840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32775 v h) (hints_cons _ _ _ (der_77840 v h) (by intro d hd; cases hd)))
def cl_77846 : CNF.NClause := [(60,false),(62,true),(74,false),(80,false),(68,false)]
theorem der_77846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77846 :=
  CNF.rup_sound cl_77846 [cl_32779,cl_47026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32779 v h) (hints_cons _ _ _ (der_47026 v h) (by intro d hd; cases hd)))
def cl_77848 : CNF.NClause := [(68,true),(60,false),(74,false),(80,false),(86,true)]
theorem der_77848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77848 :=
  CNF.rup_sound cl_77848 [cl_32784,cl_77831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32784 v h) (hints_cons _ _ _ (der_77831 v h) (by intro d hd; cases hd)))
def cl_77850 : CNF.NClause := [(60,false),(62,true),(80,false),(68,false),(74,true)]
theorem der_77850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77850 :=
  CNF.rup_sound cl_77850 [cl_32788,cl_77837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32788 v h) (hints_cons _ _ _ (der_77837 v h) (by intro d hd; cases hd)))
def cl_77851 : CNF.NClause := [(60,false),(29,false),(80,false),(62,false),(74,true)]
theorem der_77851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77851 :=
  CNF.rup_sound cl_77851 [cl_32789,cl_77836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32789 v h) (hints_cons _ _ _ (der_77836 v h) (by intro d hd; cases hd)))
def cl_77852 : CNF.NClause := [(60,false),(62,false),(80,false),(68,true),(74,true)]
theorem der_77852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77852 :=
  CNF.rup_sound cl_77852 [cl_32790,cl_77851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32790 v h) (hints_cons _ _ _ (der_77851 v h) (by intro d hd; cases hd)))
def cl_77854 : CNF.NClause := [(62,true),(86,true),(80,false),(60,false),(68,true)]
theorem der_77854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77854 :=
  CNF.rup_sound cl_77854 [cl_32792,cl_77829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32792 v h) (hints_cons _ _ _ (der_77829 v h) (by intro d hd; cases hd)))
def cl_77855 : CNF.NClause := [(60,false),(86,true),(62,false),(74,false),(29,false)]
theorem der_77855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77855 :=
  CNF.rup_sound cl_77855 [cl_32793,cl_50867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32793 v h) (hints_cons _ _ _ (der_50867 v h) (by intro d hd; cases hd)))
def cl_77857 : CNF.NClause := [(60,false),(80,true),(68,false),(62,true),(74,false)]
theorem der_77857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77857 :=
  CNF.rup_sound cl_77857 [cl_32795,cl_77830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32795 v h) (hints_cons _ _ _ (der_77830 v h) (by intro d hd; cases hd)))
def cl_77858 : CNF.NClause := [(60,false),(29,false),(62,false),(74,true),(68,false)]
theorem der_77858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77858 :=
  CNF.rup_sound cl_77858 [cl_32800,cl_32785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32800 v h) (hints_cons _ _ _ (der_32785 v h) (by intro d hd; cases hd)))
def cl_77859 : CNF.NClause := [(60,false),(86,true),(62,false),(74,true),(68,false)]
theorem der_77859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77859 :=
  CNF.rup_sound cl_77859 [cl_32801,cl_77858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32801 v h) (hints_cons _ _ _ (der_77858 v h) (by intro d hd; cases hd)))
def cl_77860 : CNF.NClause := [(86,true),(74,true),(29,false),(60,false),(68,false)]
theorem der_77860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77860 :=
  CNF.rup_sound cl_77860 [cl_32802,cl_77859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32802 v h) (hints_cons _ _ _ (der_77859 v h) (by intro d hd; cases hd)))
def cl_77861 : CNF.NClause := [(60,false),(68,true),(29,false),(80,true),(86,true)]
theorem der_77861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77861 :=
  CNF.rup_sound cl_77861 [cl_52298,cl_50865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52298 v h) (hints_cons _ _ _ (der_50865 v h) (by intro d hd; cases hd)))
def cl_77862 : CNF.NClause := [(55,false),(91,false),(63,false),(67,true),(80,false)]
theorem der_77862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77862 :=
  CNF.rup_sound cl_77862 [cl_52300,cl_77082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52300 v h) (hints_cons _ _ _ (der_77082 v h) (by intro d hd; cases hd)))
def cl_77863 : CNF.NClause := [(55,false),(63,true),(84,false),(80,false),(76,false)]
theorem der_77863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77863 :=
  CNF.rup_sound cl_77863 [cl_52301,cl_77425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52301 v h) (hints_cons _ _ _ (der_77425 v h) (by intro d hd; cases hd)))
def cl_77864 : CNF.NClause := [(55,false),(80,false),(84,false),(24,false),(67,true)]
theorem der_77864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77864 :=
  CNF.rup_sound cl_77864 [cl_52304,cl_50880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52304 v h) (hints_cons _ _ _ (der_50880 v h) (by intro d hd; cases hd)))
def cl_77866 : CNF.NClause := [(55,false),(80,true),(84,false),(91,false),(76,false)]
theorem der_77866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77866 :=
  CNF.rup_sound cl_77866 [cl_37298,cl_50869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37298 v h) (hints_cons _ _ _ (der_50869 v h) (by intro d hd; cases hd)))
def cl_77867 : CNF.NClause := [(55,false),(67,true),(84,false),(63,false),(91,false)]
theorem der_77867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77867 :=
  CNF.rup_sound cl_77867 [cl_32812,cl_50885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32812 v h) (hints_cons _ _ _ (der_50885 v h) (by intro d hd; cases hd)))
def cl_77870 : CNF.NClause := [(55,false),(80,true),(84,false),(24,false),(91,false)]
theorem der_77870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77870 :=
  CNF.rup_sound cl_77870 [cl_32819,cl_77866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32819 v h) (hints_cons _ _ _ (der_77866 v h) (by intro d hd; cases hd)))
def cl_77871 : CNF.NClause := [(55,false),(84,false),(91,false),(67,true),(24,true)]
theorem der_77871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77871 :=
  CNF.rup_sound cl_77871 [cl_32820,cl_77867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32820 v h) (hints_cons _ _ _ (der_77867 v h) (by intro d hd; cases hd)))
def cl_77872 : CNF.NClause := [(55,false),(91,false),(80,false),(84,true),(63,false)]
theorem der_77872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77872 :=
  CNF.rup_sound cl_77872 [cl_32822,cl_77082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32822 v h) (hints_cons _ _ _ (der_77082 v h) (by intro d hd; cases hd)))
def cl_77876 : CNF.NClause := [(55,false),(24,true),(67,false),(63,false),(84,true)]
theorem der_77876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77876 :=
  CNF.rup_sound cl_77876 [cl_52313,cl_50893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52313 v h) (hints_cons _ _ _ (der_50893 v h) (by intro d hd; cases hd)))
def cl_77877 : CNF.NClause := [(55,false),(63,true),(76,false),(67,false),(91,false)]
theorem der_77877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77877 :=
  CNF.rup_sound cl_77877 [cl_32832,cl_52054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32832 v h) (hints_cons _ _ _ (der_52054 v h) (by intro d hd; cases hd)))
def cl_77879 : CNF.NClause := [(55,false),(67,true),(76,false),(91,false),(63,false)]
theorem der_77879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77879 :=
  CNF.rup_sound cl_77879 [cl_32834,cl_77862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32834 v h) (hints_cons _ _ _ (der_77862 v h) (by intro d hd; cases hd)))
def cl_77880 : CNF.NClause := [(55,false),(63,true),(67,false),(84,false),(76,false)]
theorem der_77880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77880 :=
  CNF.rup_sound cl_77880 [cl_52316,cl_77425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52316 v h) (hints_cons _ _ _ (der_77425 v h) (by intro d hd; cases hd)))
def cl_77881 : CNF.NClause := [(55,false),(67,true),(76,false),(84,false),(80,false)]
theorem der_77881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77881 :=
  CNF.rup_sound cl_77881 [cl_32845,cl_77863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32845 v h) (hints_cons _ _ _ (der_77863 v h) (by intro d hd; cases hd)))
def cl_77882 : CNF.NClause := [(55,false),(91,true),(76,false),(84,false),(80,false)]
theorem der_77882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77882 :=
  CNF.rup_sound cl_77882 [cl_52317,cl_77425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52317 v h) (hints_cons _ _ _ (der_77425 v h) (by intro d hd; cases hd)))
def cl_77883 : CNF.NClause := [(55,false),(80,false),(76,true),(63,false),(84,false)]
theorem der_77883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77883 :=
  CNF.rup_sound cl_77883 [cl_52318,cl_77083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52318 v h) (hints_cons _ _ _ (der_77083 v h) (by intro d hd; cases hd)))
def cl_77884 : CNF.NClause := [(55,false),(84,false),(67,false),(80,false),(76,true)]
theorem der_77884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77884 :=
  CNF.rup_sound cl_77884 [cl_32848,cl_50879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32848 v h) (hints_cons _ _ _ (der_50879 v h) (by intro d hd; cases hd)))
def cl_77885 : CNF.NClause := [(55,false),(63,false),(84,false),(80,false),(76,true)]
theorem der_77885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77885 :=
  CNF.rup_sound cl_77885 [cl_32850,cl_77083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32850 v h) (hints_cons _ _ _ (der_77083 v h) (by intro d hd; cases hd)))
def cl_77886 : CNF.NClause := [(55,false),(91,true),(84,false),(80,false),(67,true)]
theorem der_77886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77886 :=
  CNF.rup_sound cl_77886 [cl_32852,cl_77083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32852 v h) (hints_cons _ _ _ (der_77083 v h) (by intro d hd; cases hd)))
def cl_77887 : CNF.NClause := [(55,false),(80,true),(84,false),(24,false),(67,false)]
theorem der_77887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77887 :=
  CNF.rup_sound cl_77887 [cl_52319,cl_50894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52319 v h) (hints_cons _ _ _ (der_50894 v h) (by intro d hd; cases hd)))
def cl_77890 : CNF.NClause := [(55,false),(67,true),(84,false),(63,false),(76,false)]
theorem der_77890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77890 :=
  CNF.rup_sound cl_77890 [cl_32857,cl_77425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32857 v h) (hints_cons _ _ _ (der_77425 v h) (by intro d hd; cases hd)))
def cl_77891 : CNF.NClause := [(55,false),(63,true),(76,false),(84,false),(80,true)]
theorem der_77891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77891 :=
  CNF.rup_sound cl_77891 [cl_32858,cl_77425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32858 v h) (hints_cons _ _ _ (der_77425 v h) (by intro d hd; cases hd)))
def cl_77893 : CNF.NClause := [(55,false),(63,true),(67,false),(84,false),(91,true)]
theorem der_77893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77893 :=
  CNF.rup_sound cl_77893 [cl_32862,cl_50883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32862 v h) (hints_cons _ _ _ (der_50883 v h) (by intro d hd; cases hd)))
def cl_77894 : CNF.NClause := [(55,false),(91,true),(84,false),(76,true),(67,true)]
theorem der_77894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77894 :=
  CNF.rup_sound cl_77894 [cl_32867,cl_77886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32867 v h) (hints_cons _ _ _ (der_77886 v h) (by intro d hd; cases hd)))
def cl_77896 : CNF.NClause := [(55,false),(76,false),(84,true),(80,false),(67,false)]
theorem der_77896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77896 :=
  CNF.rup_sound cl_77896 [cl_32868,cl_52054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32868 v h) (hints_cons _ _ _ (der_52054 v h) (by intro d hd; cases hd)))
def cl_77899 : CNF.NClause := [(55,false),(67,true),(24,false),(80,false),(76,false)]
theorem der_77899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77899 :=
  CNF.rup_sound cl_77899 [cl_32873,cl_77864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32873 v h) (hints_cons _ _ _ (der_77864 v h) (by intro d hd; cases hd)))
def cl_77903 : CNF.NClause := [(55,false),(63,true),(24,true),(67,false),(80,false)]
theorem der_77903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77903 :=
  CNF.rup_sound cl_77903 [cl_32877,cl_52054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32877 v h) (hints_cons _ _ _ (der_52054 v h) (by intro d hd; cases hd)))
def cl_77904 : CNF.NClause := [(55,false),(76,true),(63,false),(80,false),(67,true)]
theorem der_77904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77904 :=
  CNF.rup_sound cl_77904 [cl_32878,cl_77084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32878 v h) (hints_cons _ _ _ (der_77084 v h) (by intro d hd; cases hd)))
def cl_77905 : CNF.NClause := [(55,false),(24,true),(76,true),(67,true),(80,false)]
theorem der_77905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77905 :=
  CNF.rup_sound cl_77905 [cl_52322,cl_77083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52322 v h) (hints_cons _ _ _ (der_77083 v h) (by intro d hd; cases hd)))
def cl_77907 : CNF.NClause := [(55,false),(91,true),(67,false),(84,true),(76,false)]
theorem der_77907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77907 :=
  CNF.rup_sound cl_77907 [cl_32881,cl_50890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32881 v h) (hints_cons _ _ _ (der_50890 v h) (by intro d hd; cases hd)))
def cl_77908 : CNF.NClause := [(55,false),(80,true),(76,false),(24,true),(67,true)]
theorem der_77908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77908 :=
  CNF.rup_sound cl_77908 [cl_52324,cl_77425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52324 v h) (hints_cons _ _ _ (der_77425 v h) (by intro d hd; cases hd)))
def cl_77911 : CNF.NClause := [(46,false),(80,false),(77,true),(81,false),(78,false)]
theorem der_77911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77911 :=
  CNF.rup_sound cl_77911 [cl_52329,cl_50921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52329 v h) (hints_cons _ _ _ (der_50921 v h) (by intro d hd; cases hd)))
def cl_77913 : CNF.NClause := [(46,false),(15,false),(78,true),(77,false),(81,false)]
theorem der_77913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77913 :=
  CNF.rup_sound cl_77913 [cl_52332,cl_50917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52332 v h) (hints_cons _ _ _ (der_50917 v h) (by intro d hd; cases hd)))
def cl_77914 : CNF.NClause := [(46,false),(77,true),(81,false),(92,false),(79,false)]
theorem der_77914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77914 :=
  CNF.rup_sound cl_77914 [cl_32901,cl_50899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32901 v h) (hints_cons _ _ _ (der_50899 v h) (by intro d hd; cases hd)))
def cl_77916 : CNF.NClause := [(46,false),(78,false),(80,true),(92,false),(81,false)]
theorem der_77916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77916 :=
  CNF.rup_sound cl_77916 [cl_32905,cl_52333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32905 v h) (hints_cons _ _ _ (der_52333 v h) (by intro d hd; cases hd)))
def cl_77917 : CNF.NClause := [(46,false),(77,true),(92,false),(81,false),(78,true)]
theorem der_77917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77917 :=
  CNF.rup_sound cl_77917 [cl_32909,cl_77914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32909 v h) (hints_cons _ _ _ (der_77914 v h) (by intro d hd; cases hd)))
def cl_77920 : CNF.NClause := [(46,false),(15,true),(80,false),(92,false),(79,false)]
theorem der_77920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77920 :=
  CNF.rup_sound cl_77920 [cl_32912,cl_50901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32912 v h) (hints_cons _ _ _ (der_50901 v h) (by intro d hd; cases hd)))
def cl_77921 : CNF.NClause := [(46,false),(15,false),(80,false),(79,true),(77,false)]
theorem der_77921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77921 :=
  CNF.rup_sound cl_77921 [cl_52337,cl_50924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52337 v h) (hints_cons _ _ _ (der_50924 v h) (by intro d hd; cases hd)))
def cl_77923 : CNF.NClause := [(46,false),(15,false),(80,false),(79,true),(92,false)]
theorem der_77923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77923 :=
  CNF.rup_sound cl_77923 [cl_52338,cl_52327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52338 v h) (hints_cons _ _ _ (der_52327 v h) (by intro d hd; cases hd)))
def cl_77924 : CNF.NClause := [(46,false),(15,true),(92,false),(78,false),(79,false)]
theorem der_77924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77924 :=
  CNF.rup_sound cl_77924 [cl_32921,cl_50925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32921 v h) (hints_cons _ _ _ (der_50925 v h) (by intro d hd; cases hd)))
def cl_77926 : CNF.NClause := [(46,false),(81,true),(15,false),(92,false),(78,true)]
theorem der_77926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77926 :=
  CNF.rup_sound cl_77926 [cl_32924,cl_50908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32924 v h) (hints_cons _ _ _ (der_50908 v h) (by intro d hd; cases hd)))
def cl_77927 : CNF.NClause := [(46,false),(80,true),(92,false),(78,false),(15,false)]
theorem der_77927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77927 :=
  CNF.rup_sound cl_77927 [cl_32926,cl_50905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32926 v h) (hints_cons _ _ _ (der_50905 v h) (by intro d hd; cases hd)))
def cl_77928 : CNF.NClause := [(46,false),(92,true),(79,false),(81,false),(78,false)]
theorem der_77928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77928 :=
  CNF.rup_sound cl_77928 [cl_52341,cl_77560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52341 v h) (hints_cons _ _ _ (der_77560 v h) (by intro d hd; cases hd)))
def cl_77931 : CNF.NClause := [(46,false),(80,false),(81,false),(77,true),(79,false)]
theorem der_77931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77931 :=
  CNF.rup_sound cl_77931 [cl_32935,cl_50915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32935 v h) (hints_cons _ _ _ (der_50915 v h) (by intro d hd; cases hd)))
def cl_77932 : CNF.NClause := [(46,false),(92,true),(81,false),(78,false),(80,false)]
theorem der_77932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77932 :=
  CNF.rup_sound cl_77932 [cl_32937,cl_77911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32937 v h) (hints_cons _ _ _ (der_77911 v h) (by intro d hd; cases hd)))
def cl_77933 : CNF.NClause := [(46,false),(92,true),(77,false),(81,false),(15,false)]
theorem der_77933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77933 :=
  CNF.rup_sound cl_77933 [cl_52345,cl_50917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52345 v h) (hints_cons _ _ _ (der_50917 v h) (by intro d hd; cases hd)))
def cl_77934 : CNF.NClause := [(46,false),(81,false),(15,true),(77,false),(78,false)]
theorem der_77934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77934 :=
  CNF.rup_sound cl_77934 [cl_32950,cl_62905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32950 v h) (hints_cons _ _ _ (der_62905 v h) (by intro d hd; cases hd)))
def cl_77935 : CNF.NClause := [(46,false),(77,true),(81,false),(78,false),(15,false)]
theorem der_77935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77935 :=
  CNF.rup_sound cl_77935 [cl_32951,cl_77911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32951 v h) (hints_cons _ _ _ (der_77911 v h) (by intro d hd; cases hd)))
def cl_77936 : CNF.NClause := [(46,false),(77,true),(92,true),(78,false),(81,false)]
theorem der_77936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77936 :=
  CNF.rup_sound cl_77936 [cl_32952,cl_77935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32952 v h) (hints_cons _ _ _ (der_77935 v h) (by intro d hd; cases hd)))
def cl_77938 : CNF.NClause := [(46,false),(15,false),(80,false),(79,false),(78,true)]
theorem der_77938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77938 :=
  CNF.rup_sound cl_77938 [cl_32959,cl_50919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32959 v h) (hints_cons _ _ _ (der_50919 v h) (by intro d hd; cases hd)))
def cl_77939 : CNF.NClause := [(46,false),(92,true),(77,false),(80,false),(15,false)]
theorem der_77939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77939 :=
  CNF.rup_sound cl_77939 [cl_32963,cl_50923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32963 v h) (hints_cons _ _ _ (der_50923 v h) (by intro d hd; cases hd)))
def cl_77940 : CNF.NClause := [(46,false),(77,false),(80,false),(15,true),(78,false)]
theorem der_77940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77940 :=
  CNF.rup_sound cl_77940 [cl_32964,cl_62905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32964 v h) (hints_cons _ _ _ (der_62905 v h) (by intro d hd; cases hd)))
def cl_77941 : CNF.NClause := [(46,false),(15,false),(80,false),(78,false),(77,true)]
theorem der_77941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77941 :=
  CNF.rup_sound cl_77941 [cl_32965,cl_77911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32965 v h) (hints_cons _ _ _ (der_77911 v h) (by intro d hd; cases hd)))
def cl_77942 : CNF.NClause := [(46,false),(81,true),(78,false),(79,false),(15,false)]
theorem der_77942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77942 :=
  CNF.rup_sound cl_77942 [cl_32971,cl_77565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32971 v h) (hints_cons _ _ _ (der_77565 v h) (by intro d hd; cases hd)))
def cl_77943 : CNF.NClause := [(46,false),(92,true),(79,false),(78,true),(15,false)]
theorem der_77943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77943 :=
  CNF.rup_sound cl_77943 [cl_32976,cl_77938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32976 v h) (hints_cons _ _ _ (der_77938 v h) (by intro d hd; cases hd)))
def cl_77944 : CNF.NClause := [(46,false),(15,false),(79,true),(77,false),(81,true)]
theorem der_77944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77944 :=
  CNF.rup_sound cl_77944 [cl_32981,cl_77921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32981 v h) (hints_cons _ _ _ (der_77921 v h) (by intro d hd; cases hd)))
def cl_77945 : CNF.NClause := [(46,false),(81,true),(15,false),(80,true),(78,true)]
theorem der_77945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77945 :=
  CNF.rup_sound cl_77945 [cl_32983,cl_77926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32983 v h) (hints_cons _ _ _ (der_77926 v h) (by intro d hd; cases hd)))
def cl_77946 : CNF.NClause := [(46,false),(81,true),(77,true),(80,true),(78,true)]
theorem der_77946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77946 :=
  CNF.rup_sound cl_77946 [cl_32984,cl_77945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32984 v h) (hints_cons _ _ _ (der_77945 v h) (by intro d hd; cases hd)))
def cl_77947 : CNF.NClause := [(42,false),(72,false),(80,false),(11,true),(83,false)]
theorem der_77947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77947 :=
  CNF.rup_sound cl_77947 [cl_52349,cl_50939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52349 v h) (hints_cons _ _ _ (der_50939 v h) (by intro d hd; cases hd)))
def cl_77948 : CNF.NClause := [(42,false),(66,true),(90,false),(83,false),(69,false)]
theorem der_77948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77948 :=
  CNF.rup_sound cl_77948 [cl_52350,cl_50935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52350 v h) (hints_cons _ _ _ (der_50935 v h) (by intro d hd; cases hd)))
def cl_77949 : CNF.NClause := [(72,true),(42,false),(80,false),(69,false),(66,false)]
theorem der_77949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77949 :=
  CNF.rup_sound cl_77949 [cl_48429,cl_50946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48429 v h) (hints_cons _ _ _ (der_50946 v h) (by intro d hd; cases hd)))
def cl_77950 : CNF.NClause := [(42,false),(83,false),(69,true),(90,false),(80,false)]
theorem der_77950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77950 :=
  CNF.rup_sound cl_77950 [cl_32986,cl_50927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32986 v h) (hints_cons _ _ _ (der_50927 v h) (by intro d hd; cases hd)))
def cl_77951 : CNF.NClause := [(42,false),(83,false),(69,true),(72,false),(90,false)]
theorem der_77951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77951 :=
  CNF.rup_sound cl_77951 [cl_52360,cl_52093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52360 v h) (hints_cons _ _ _ (der_52093 v h) (by intro d hd; cases hd)))
def cl_77952 : CNF.NClause := [(42,false),(80,true),(69,false),(90,false),(83,false)]
theorem der_77952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77952 :=
  CNF.rup_sound cl_77952 [cl_32990,cl_77948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32990 v h) (hints_cons _ _ _ (der_77948 v h) (by intro d hd; cases hd)))
def cl_77953 : CNF.NClause := [(42,false),(69,true),(83,false),(90,false),(11,false)]
theorem der_77953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77953 :=
  CNF.rup_sound cl_77953 [cl_32993,cl_50929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32993 v h) (hints_cons _ _ _ (der_50929 v h) (by intro d hd; cases hd)))
def cl_77954 : CNF.NClause := [(42,false),(83,false),(90,false),(69,true),(66,false)]
theorem der_77954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77954 :=
  CNF.rup_sound cl_77954 [cl_32994,cl_52093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32994 v h) (hints_cons _ _ _ (der_52093 v h) (by intro d hd; cases hd)))
def cl_77956 : CNF.NClause := [(42,false),(90,false),(80,false),(72,false),(11,true)]
theorem der_77956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77956 :=
  CNF.rup_sound cl_77956 [cl_33000,cl_52361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33000 v h) (hints_cons _ _ _ (der_52361 v h) (by intro d hd; cases hd)))
def cl_77957 : CNF.NClause := [(42,false),(69,true),(90,false),(11,false),(80,false)]
theorem der_77957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77957 :=
  CNF.rup_sound cl_77957 [cl_33003,cl_50932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33003 v h) (hints_cons _ _ _ (der_50932 v h) (by intro d hd; cases hd)))
def cl_77958 : CNF.NClause := [(42,false),(80,true),(90,false),(66,false),(72,false)]
theorem der_77958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77958 :=
  CNF.rup_sound cl_77958 [cl_33006,cl_52093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33006 v h) (hints_cons _ _ _ (der_52093 v h) (by intro d hd; cases hd)))
def cl_77960 : CNF.NClause := [(42,false),(80,true),(11,false),(69,false),(90,false)]
theorem der_77960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77960 :=
  CNF.rup_sound cl_77960 [cl_33013,cl_50934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33013 v h) (hints_cons _ _ _ (der_50934 v h) (by intro d hd; cases hd)))
def cl_77961 : CNF.NClause := [(72,true),(42,false),(11,true),(66,false),(83,true)]
theorem der_77961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77961 :=
  CNF.rup_sound cl_77961 [cl_52365,cl_50956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52365 v h) (hints_cons _ _ _ (der_50956 v h) (by intro d hd; cases hd)))
def cl_77963 : CNF.NClause := [(42,false),(83,false),(69,true),(80,false),(72,false)]
theorem der_77963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77963 :=
  CNF.rup_sound cl_77963 [cl_52369,cl_77950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52369 v h) (hints_cons _ _ _ (der_77950 v h) (by intro d hd; cases hd)))
def cl_77964 : CNF.NClause := [(42,false),(66,true),(11,false),(80,false),(69,false)]
theorem der_77964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77964 :=
  CNF.rup_sound cl_77964 [cl_33022,cl_50944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33022 v h) (hints_cons _ _ _ (der_50944 v h) (by intro d hd; cases hd)))
def cl_77966 : CNF.NClause := [(66,true),(72,true),(42,false),(80,false),(11,false)]
theorem der_77966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77966 :=
  CNF.rup_sound cl_77966 [cl_33025,cl_50947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33025 v h) (hints_cons _ _ _ (der_50947 v h) (by intro d hd; cases hd)))
def cl_77968 : CNF.NClause := [(42,false),(69,true),(11,false),(66,false),(72,false)]
theorem der_77968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77968 :=
  CNF.rup_sound cl_77968 [cl_33030,cl_50955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33030 v h) (hints_cons _ _ _ (der_50955 v h) (by intro d hd; cases hd)))
def cl_77969 : CNF.NClause := [(42,false),(83,false),(72,false),(11,true),(66,false)]
theorem der_77969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77969 :=
  CNF.rup_sound cl_77969 [cl_33031,cl_77947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33031 v h) (hints_cons _ _ _ (der_77947 v h) (by intro d hd; cases hd)))
def cl_77971 : CNF.NClause := [(42,false),(11,true),(90,true),(72,false),(83,false)]
theorem der_77971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77971 :=
  CNF.rup_sound cl_77971 [cl_52373,cl_77969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52373 v h) (hints_cons _ _ _ (der_77969 v h) (by intro d hd; cases hd)))
def cl_77973 : CNF.NClause := [(72,true),(42,false),(83,false),(90,true),(69,false)]
theorem der_77973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77973 :=
  CNF.rup_sound cl_77973 [cl_33034,cl_77086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33034 v h) (hints_cons _ _ _ (der_77086 v h) (by intro d hd; cases hd)))
def cl_77974 : CNF.NClause := [(42,false),(72,true),(80,true),(66,false),(69,true)]
theorem der_77974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77974 :=
  CNF.rup_sound cl_77974 [cl_33038,cl_50956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33038 v h) (hints_cons _ _ _ (der_50956 v h) (by intro d hd; cases hd)))
def cl_77978 : CNF.NClause := [(42,false),(83,true),(90,true),(80,false),(66,false)]
theorem der_77978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77978 :=
  CNF.rup_sound cl_77978 [cl_52377,cl_50945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52377 v h) (hints_cons _ _ _ (der_50945 v h) (by intro d hd; cases hd)))
def cl_77980 : CNF.NClause := [(42,false),(72,true),(80,false),(90,true),(69,false)]
theorem der_77980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77980 :=
  CNF.rup_sound cl_77980 [cl_33048,cl_77949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33048 v h) (hints_cons _ _ _ (der_77949 v h) (by intro d hd; cases hd)))
def cl_77981 : CNF.NClause := [(42,false),(83,true),(66,false),(69,false),(72,false)]
theorem der_77981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77981 :=
  CNF.rup_sound cl_77981 [cl_33053,cl_58640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33053 v h) (hints_cons _ _ _ (der_58640 v h) (by intro d hd; cases hd)))
def cl_77982 : CNF.NClause := [(42,false),(11,true),(80,true),(66,false),(69,true)]
theorem der_77982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77982 :=
  CNF.rup_sound cl_77982 [cl_52378,cl_77974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52378 v h) (hints_cons _ _ _ (der_77974 v h) (by intro d hd; cases hd)))
def cl_77983 : CNF.NClause := [(42,false),(83,true),(90,true),(66,false),(69,false)]
theorem der_77983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77983 :=
  CNF.rup_sound cl_77983 [cl_33060,cl_58640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33060 v h) (hints_cons _ _ _ (der_58640 v h) (by intro d hd; cases hd)))
def cl_77984 : CNF.NClause := [(34,false),(75,true),(70,false),(87,false),(85,false)]
theorem der_77984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77984 :=
  CNF.rup_sound cl_77984 [cl_52383,cl_50425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52383 v h) (hints_cons _ _ _ (der_50425 v h) (by intro d hd; cases hd)))
def cl_77985 : CNF.NClause := [(75,true),(3,false),(34,false),(87,false),(85,false)]
theorem der_77985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77985 :=
  CNF.rup_sound cl_77985 [cl_52386,cl_77984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52386 v h) (hints_cons _ _ _ (der_77984 v h) (by intro d hd; cases hd)))
def cl_77986 : CNF.NClause := [(34,false),(87,false),(85,false),(70,true),(80,false)]
theorem der_77986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77986 :=
  CNF.rup_sound cl_77986 [cl_33069,cl_61004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33069 v h) (hints_cons _ _ _ (der_61004 v h) (by intro d hd; cases hd)))
def cl_77991 : CNF.NClause := [(34,false),(65,true),(87,false),(3,false),(75,false)]
theorem der_77991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77991 :=
  CNF.rup_sound cl_77991 [cl_33081,cl_77093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33081 v h) (hints_cons _ _ _ (der_77093 v h) (by intro d hd; cases hd)))
def cl_77992 : CNF.NClause := [(34,false),(85,true),(87,false),(3,false),(70,false)]
theorem der_77992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77992 :=
  CNF.rup_sound cl_77992 [cl_52391,cl_50990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52391 v h) (hints_cons _ _ _ (der_50990 v h) (by intro d hd; cases hd)))
def cl_77993 : CNF.NClause := [(34,false),(85,true),(87,false),(65,false),(70,false)]
theorem der_77993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77993 :=
  CNF.rup_sound cl_77993 [cl_52392,cl_50970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52392 v h) (hints_cons _ _ _ (der_50970 v h) (by intro d hd; cases hd)))
def cl_77994 : CNF.NClause := [(34,false),(87,false),(80,false),(65,false),(70,true)]
theorem der_77994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77994 :=
  CNF.rup_sound cl_77994 [cl_33085,cl_61004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33085 v h) (hints_cons _ _ _ (der_61004 v h) (by intro d hd; cases hd)))
def cl_77996 : CNF.NClause := [(34,false),(80,true),(75,false),(87,false),(65,false)]
theorem der_77996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77996 :=
  CNF.rup_sound cl_77996 [cl_33091,cl_50970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33091 v h) (hints_cons _ _ _ (der_50970 v h) (by intro d hd; cases hd)))
def cl_77998 : CNF.NClause := [(34,false),(65,true),(80,false),(75,false),(70,false)]
theorem der_77998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77998 :=
  CNF.rup_sound cl_77998 [cl_33102,cl_77092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33102 v h) (hints_cons _ _ _ (der_77092 v h) (by intro d hd; cases hd)))
def cl_78001 : CNF.NClause := [(34,false),(3,true),(75,false),(70,true),(80,false)]
theorem der_78001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78001 :=
  CNF.rup_sound cl_78001 [cl_33104,cl_77092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33104 v h) (hints_cons _ _ _ (der_77092 v h) (by intro d hd; cases hd)))
def cl_78002 : CNF.NClause := [(34,false),(75,true),(85,false),(3,false),(80,false)]
theorem der_78002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78002 :=
  CNF.rup_sound cl_78002 [cl_52401,cl_77985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52401 v h) (hints_cons _ _ _ (der_77985 v h) (by intro d hd; cases hd)))
def cl_78003 : CNF.NClause := [(34,false),(65,true),(3,true),(70,false),(80,false)]
theorem der_78003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78003 :=
  CNF.rup_sound cl_78003 [cl_33105,cl_50981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33105 v h) (hints_cons _ _ _ (der_50981 v h) (by intro d hd; cases hd)))
def cl_78004 : CNF.NClause := [(34,false),(80,false),(85,false),(70,true),(65,false)]
theorem der_78004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78004 :=
  CNF.rup_sound cl_78004 [cl_33107,cl_77986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33107 v h) (hints_cons _ _ _ (der_77986 v h) (by intro d hd; cases hd)))
def cl_78005 : CNF.NClause := [(34,false),(75,true),(85,false),(3,false),(70,true)]
theorem der_78005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78005 :=
  CNF.rup_sound cl_78005 [cl_33108,cl_50977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33108 v h) (hints_cons _ _ _ (der_50977 v h) (by intro d hd; cases hd)))
def cl_78007 : CNF.NClause := [(34,false),(65,true),(3,false),(70,false),(75,false)]
theorem der_78007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78007 :=
  CNF.rup_sound cl_78007 [cl_33111,cl_50990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33111 v h) (hints_cons _ _ _ (der_50990 v h) (by intro d hd; cases hd)))
def cl_78009 : CNF.NClause := [(34,false),(75,true),(3,false),(85,false),(65,false)]
theorem der_78009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78009 :=
  CNF.rup_sound cl_78009 [cl_52403,cl_77985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52403 v h) (hints_cons _ _ _ (der_77985 v h) (by intro d hd; cases hd)))
def cl_78011 : CNF.NClause := [(34,false),(65,true),(75,true),(80,true),(85,false)]
theorem der_78011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78011 :=
  CNF.rup_sound cl_78011 [cl_52404,cl_50978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52404 v h) (hints_cons _ _ _ (der_50978 v h) (by intro d hd; cases hd)))
def cl_78012 : CNF.NClause := [(34,false),(75,true),(85,false),(80,true),(3,true)]
theorem der_78012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78012 :=
  CNF.rup_sound cl_78012 [cl_33120,cl_78011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33120 v h) (hints_cons _ _ _ (der_78011 v h) (by intro d hd; cases hd)))
def cl_78013 : CNF.NClause := [(34,false),(85,true),(70,false),(75,false),(3,false)]
theorem der_78013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78013 :=
  CNF.rup_sound cl_78013 [cl_52405,cl_50985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52405 v h) (hints_cons _ _ _ (der_50985 v h) (by intro d hd; cases hd)))
def cl_78017 : CNF.NClause := [(34,false),(3,false),(85,true),(70,true),(75,false)]
theorem der_78017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78017 :=
  CNF.rup_sound cl_78017 [cl_33127,cl_77093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33127 v h) (hints_cons _ _ _ (der_77093 v h) (by intro d hd; cases hd)))
def cl_78018 : CNF.NClause := [(34,false),(65,false),(3,true),(85,true),(80,false)]
theorem der_78018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78018 :=
  CNF.rup_sound cl_78018 [cl_52408,cl_53652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52408 v h) (hints_cons _ _ _ (der_53652 v h) (by intro d hd; cases hd)))
def cl_78019 : CNF.NClause := [(70,true),(65,true),(3,true),(34,false),(80,false)]
theorem der_78019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78019 :=
  CNF.rup_sound cl_78019 [cl_33134,cl_78001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33134 v h) (hints_cons _ _ _ (der_78001 v h) (by intro d hd; cases hd)))
def cl_78021 : CNF.NClause := [(34,false),(80,true),(85,true),(75,true),(87,true)]
theorem der_78021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78021 :=
  CNF.rup_sound cl_78021 [cl_52410,cl_50992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52410 v h) (hints_cons _ _ _ (der_50992 v h) (by intro d hd; cases hd)))
def cl_78022 : CNF.NClause := [(34,false),(65,true),(70,false),(80,true),(75,true)]
theorem der_78022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78022 :=
  CNF.rup_sound cl_78022 [cl_33144,cl_78011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33144 v h) (hints_cons _ _ _ (der_78011 v h) (by intro d hd; cases hd)))
def cl_78023 : CNF.NClause := [(34,false),(87,true),(3,false),(75,true),(65,false)]
theorem der_78023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78023 :=
  CNF.rup_sound cl_78023 [cl_52411,cl_78009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52411 v h) (hints_cons _ _ _ (der_78009 v h) (by intro d hd; cases hd)))
def cl_78024 : CNF.NClause := [(48,false),(17,false),(88,false),(76,true),(83,false)]
theorem der_78024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78024 :=
  CNF.rup_sound cl_78024 [cl_52413,cl_51008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52413 v h) (hints_cons _ _ _ (der_51008 v h) (by intro d hd; cases hd)))
def cl_78025 : CNF.NClause := [(48,false),(83,false),(88,false),(77,false),(76,true)]
theorem der_78025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78025 :=
  CNF.rup_sound cl_78025 [cl_33157,cl_51006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33157 v h) (hints_cons _ _ _ (der_51006 v h) (by intro d hd; cases hd)))
def cl_78029 : CNF.NClause := [(48,false),(77,true),(83,false),(88,false),(64,false)]
theorem der_78029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78029 :=
  CNF.rup_sound cl_78029 [cl_33169,cl_51021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33169 v h) (hints_cons _ _ _ (der_51021 v h) (by intro d hd; cases hd)))
def cl_78030 : CNF.NClause := [(77,true),(76,true),(83,false),(48,false),(88,false)]
theorem der_78030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78030 :=
  CNF.rup_sound cl_78030 [cl_52416,cl_78029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52416 v h) (hints_cons _ _ _ (der_78029 v h) (by intro d hd; cases hd)))
def cl_78032 : CNF.NClause := [(48,false),(77,false),(17,true),(88,false),(70,true)]
theorem der_78032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78032 :=
  CNF.rup_sound cl_78032 [cl_33174,cl_51011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33174 v h) (hints_cons _ _ _ (der_51011 v h) (by intro d hd; cases hd)))
def cl_78036 : CNF.NClause := [(48,false),(76,false),(88,false),(64,false),(17,true)]
theorem der_78036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78036 :=
  CNF.rup_sound cl_78036 [cl_33186,cl_52208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33186 v h) (hints_cons _ _ _ (der_52208 v h) (by intro d hd; cases hd)))
def cl_78038 : CNF.NClause := [(17,false),(48,false),(88,false),(77,true),(76,true)]
theorem der_78038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78038 :=
  CNF.rup_sound cl_78038 [cl_33190,cl_51013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33190 v h) (hints_cons _ _ _ (der_51013 v h) (by intro d hd; cases hd)))
def cl_78040 : CNF.NClause := [(76,true),(77,true),(88,false),(64,true),(48,false)]
theorem der_78040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78040 :=
  CNF.rup_sound cl_78040 [cl_52419,cl_78038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52419 v h) (hints_cons _ _ _ (der_78038 v h) (by intro d hd; cases hd)))
def cl_78041 : CNF.NClause := [(48,false),(83,false),(64,false),(88,true),(76,false)]
theorem der_78041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78041 :=
  CNF.rup_sound cl_78041 [cl_52420,cl_70132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52420 v h) (hints_cons _ _ _ (der_70132 v h) (by intro d hd; cases hd)))
def cl_78043 : CNF.NClause := [(17,false),(48,false),(83,false),(76,false),(70,true)]
theorem der_78043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78043 :=
  CNF.rup_sound cl_78043 [cl_52422,cl_51022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52422 v h) (hints_cons _ _ _ (der_51022 v h) (by intro d hd; cases hd)))
def cl_78044 : CNF.NClause := [(48,false),(17,false),(83,false),(64,false),(76,true)]
theorem der_78044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78044 :=
  CNF.rup_sound cl_78044 [cl_33200,cl_51021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33200 v h) (hints_cons _ _ _ (der_51021 v h) (by intro d hd; cases hd)))
def cl_78046 : CNF.NClause := [(48,false),(77,true),(83,false),(17,false),(76,false)]
theorem der_78046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78046 :=
  CNF.rup_sound cl_78046 [cl_33205,cl_51022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33205 v h) (hints_cons _ _ _ (der_51022 v h) (by intro d hd; cases hd)))
def cl_78047 : CNF.NClause := [(48,false),(17,true),(70,false),(83,false),(88,true)]
theorem der_78047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78047 :=
  CNF.rup_sound cl_78047 [cl_33206,cl_51023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33206 v h) (hints_cons _ _ _ (der_51023 v h) (by intro d hd; cases hd)))
def cl_78048 : CNF.NClause := [(70,true),(48,false),(64,true),(83,false),(76,false)]
theorem der_78048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78048 :=
  CNF.rup_sound cl_78048 [cl_33210,cl_78043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33210 v h) (hints_cons _ _ _ (der_78043 v h) (by intro d hd; cases hd)))
def cl_78049 : CNF.NClause := [(48,false),(83,false),(88,true),(64,false),(17,true)]
theorem der_78049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78049 :=
  CNF.rup_sound cl_78049 [cl_33215,cl_78041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33215 v h) (hints_cons _ _ _ (der_78041 v h) (by intro d hd; cases hd)))
def cl_78050 : CNF.NClause := [(17,false),(48,false),(76,false),(77,false),(70,true)]
theorem der_78050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78050 :=
  CNF.rup_sound cl_78050 [cl_33221,cl_51024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33221 v h) (hints_cons _ _ _ (der_51024 v h) (by intro d hd; cases hd)))
def cl_78052 : CNF.NClause := [(48,false),(64,false),(77,false),(76,true),(70,false)]
theorem der_78052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78052 :=
  CNF.rup_sound cl_78052 [cl_33225,cl_77571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33225 v h) (hints_cons _ _ _ (der_77571 v h) (by intro d hd; cases hd)))
def cl_78053 : CNF.NClause := [(48,false),(76,true),(83,true),(17,true),(70,false)]
theorem der_78053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78053 :=
  CNF.rup_sound cl_78053 [cl_52426,cl_77568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52426 v h) (hints_cons _ _ _ (der_77568 v h) (by intro d hd; cases hd)))
def cl_78056 : CNF.NClause := [(48,false),(64,true),(77,false),(70,true),(17,true)]
theorem der_78056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78056 :=
  CNF.rup_sound cl_78056 [cl_33230,cl_78032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33230 v h) (hints_cons _ _ _ (der_78032 v h) (by intro d hd; cases hd)))
def cl_78058 : CNF.NClause := [(48,false),(17,true),(76,false),(64,false),(88,true)]
theorem der_78058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78058 :=
  CNF.rup_sound cl_78058 [cl_33234,cl_78041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33234 v h) (hints_cons _ _ _ (der_78041 v h) (by intro d hd; cases hd)))
def cl_78059 : CNF.NClause := [(48,false),(77,true),(76,false),(70,true),(64,true)]
theorem der_78059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78059 :=
  CNF.rup_sound cl_78059 [cl_33236,cl_78048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33236 v h) (hints_cons _ _ _ (der_78048 v h) (by intro d hd; cases hd)))
def cl_78060 : CNF.NClause := [(48,false),(76,true),(83,true),(17,true),(64,false)]
theorem der_78060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78060 :=
  CNF.rup_sound cl_78060 [cl_33240,cl_77568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33240 v h) (hints_cons _ _ _ (der_77568 v h) (by intro d hd; cases hd)))
def cl_78062 : CNF.NClause := [(76,true),(77,true),(48,false),(83,true),(17,true)]
theorem der_78062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78062 :=
  CNF.rup_sound cl_78062 [cl_33241,cl_78060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33241 v h) (hints_cons _ _ _ (der_78060 v h) (by intro d hd; cases hd)))
def cl_78065 : CNF.NClause := [(43,false),(68,true),(64,false),(91,false),(81,false)]
theorem der_78065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78065 :=
  CNF.rup_sound cl_78065 [cl_52431,cl_51048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52431 v h) (hints_cons _ _ _ (der_51048 v h) (by intro d hd; cases hd)))
def cl_78067 : CNF.NClause := [(43,false),(81,true),(72,false),(91,false),(85,false)]
theorem der_78067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78067 :=
  CNF.rup_sound cl_78067 [cl_52435,cl_51034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52435 v h) (hints_cons _ _ _ (der_51034 v h) (by intro d hd; cases hd)))
def cl_78068 : CNF.NClause := [(43,false),(68,true),(85,false),(91,false),(64,false)]
theorem der_78068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78068 :=
  CNF.rup_sound cl_78068 [cl_33252,cl_51048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33252 v h) (hints_cons _ _ _ (der_51048 v h) (by intro d hd; cases hd)))
def cl_78069 : CNF.NClause := [(43,false),(72,true),(68,false),(91,false),(85,false)]
theorem der_78069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78069 :=
  CNF.rup_sound cl_78069 [cl_52437,cl_77102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52437 v h) (hints_cons _ _ _ (der_77102 v h) (by intro d hd; cases hd)))
def cl_78072 : CNF.NClause := [(12,false),(43,false),(85,true),(72,false),(91,false)]
theorem der_78072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78072 :=
  CNF.rup_sound cl_78072 [cl_52438,cl_51044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52438 v h) (hints_cons _ _ _ (der_51044 v h) (by intro d hd; cases hd)))
def cl_78074 : CNF.NClause := [(64,true),(91,false),(43,false),(12,false),(81,false)]
theorem der_78074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78074 :=
  CNF.rup_sound cl_78074 [cl_33267,cl_51049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33267 v h) (hints_cons _ _ _ (der_51049 v h) (by intro d hd; cases hd)))
def cl_78075 : CNF.NClause := [(43,false),(81,true),(91,false),(68,false),(72,false)]
theorem der_78075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78075 :=
  CNF.rup_sound cl_78075 [cl_52442,cl_49549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52442 v h) (hints_cons _ _ _ (der_49549 v h) (by intro d hd; cases hd)))
def cl_78077 : CNF.NClause := [(43,false),(81,true),(72,false),(91,false),(64,false)]
theorem der_78077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78077 :=
  CNF.rup_sound cl_78077 [cl_52443,cl_78067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52443 v h) (hints_cons _ _ _ (der_78067 v h) (by intro d hd; cases hd)))
def cl_78079 : CNF.NClause := [(43,false),(12,true),(68,false),(91,false),(85,true)]
theorem der_78079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78079 :=
  CNF.rup_sound cl_78079 [cl_52444,cl_60853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52444 v h) (hints_cons _ _ _ (der_60853 v h) (by intro d hd; cases hd)))
def cl_78080 : CNF.NClause := [(43,false),(12,false),(91,false),(68,false),(81,true)]
theorem der_78080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78080 :=
  CNF.rup_sound cl_78080 [cl_33279,cl_78075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33279 v h) (hints_cons _ _ _ (der_78075 v h) (by intro d hd; cases hd)))
def cl_78081 : CNF.NClause := [(43,false),(12,false),(68,true),(72,false),(81,false)]
theorem der_78081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78081 :=
  CNF.rup_sound cl_78081 [cl_52446,cl_51068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52446 v h) (hints_cons _ _ _ (der_51068 v h) (by intro d hd; cases hd)))
def cl_78084 : CNF.NClause := [(43,false),(12,false),(72,true),(81,false),(85,false)]
theorem der_78084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78084 :=
  CNF.rup_sound cl_78084 [cl_52447,cl_51054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52447 v h) (hints_cons _ _ _ (der_51054 v h) (by intro d hd; cases hd)))
def cl_78085 : CNF.NClause := [(43,false),(12,false),(68,false),(64,false),(81,true)]
theorem der_78085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78085 :=
  CNF.rup_sound cl_78085 [cl_52448,cl_77099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52448 v h) (hints_cons _ _ _ (der_77099 v h) (by intro d hd; cases hd)))
def cl_78086 : CNF.NClause := [(43,false),(91,true),(81,true),(12,false),(64,false)]
theorem der_78086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78086 :=
  CNF.rup_sound cl_78086 [cl_52449,cl_62741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52449 v h) (hints_cons _ _ _ (der_62741 v h) (by intro d hd; cases hd)))
def cl_78087 : CNF.NClause := [(43,false),(12,false),(85,false),(72,true),(68,false)]
theorem der_78087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78087 :=
  CNF.rup_sound cl_78087 [cl_33302,cl_77102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33302 v h) (hints_cons _ _ _ (der_77102 v h) (by intro d hd; cases hd)))
def cl_78088 : CNF.NClause := [(43,false),(85,true),(72,false),(81,false),(68,false)]
theorem der_78088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78088 :=
  CNF.rup_sound cl_78088 [cl_52450,cl_60853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52450 v h) (hints_cons _ _ _ (der_60853 v h) (by intro d hd; cases hd)))
def cl_78091 : CNF.NClause := [(43,false),(12,true),(81,false),(64,false),(85,true)]
theorem der_78091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78091 :=
  CNF.rup_sound cl_78091 [cl_33320,cl_60853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33320 v h) (hints_cons _ _ _ (der_60853 v h) (by intro d hd; cases hd)))
def cl_78092 : CNF.NClause := [(91,true),(43,false),(64,true),(68,true),(81,false)]
theorem der_78092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78092 :=
  CNF.rup_sound cl_78092 [cl_33322,cl_77108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33322 v h) (hints_cons _ _ _ (der_77108 v h) (by intro d hd; cases hd)))
def cl_78093 : CNF.NClause := [(43,false),(85,true),(64,false),(72,false),(81,true)]
theorem der_78093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78093 :=
  CNF.rup_sound cl_78093 [cl_33328,cl_78077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33328 v h) (hints_cons _ _ _ (der_78077 v h) (by intro d hd; cases hd)))
def cl_78100 : CNF.NClause := [(33,false),(64,false),(84,false),(74,false),(79,true)]
theorem der_78100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78100 :=
  CNF.rup_sound cl_78100 [cl_52460,cl_77118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52460 v h) (hints_cons _ _ _ (der_77118 v h) (by intro d hd; cases hd)))
def cl_78101 : CNF.NClause := [(33,false),(87,false),(74,false),(84,false),(79,true)]
theorem der_78101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78101 :=
  CNF.rup_sound cl_78101 [cl_33343,cl_51084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33343 v h) (hints_cons _ _ _ (der_51084 v h) (by intro d hd; cases hd)))
def cl_78103 : CNF.NClause := [(33,false),(87,false),(69,false),(84,true),(79,false)]
theorem der_78103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78103 :=
  CNF.rup_sound cl_78103 [cl_52463,cl_51087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52463 v h) (hints_cons _ _ _ (der_51087 v h) (by intro d hd; cases hd)))
def cl_78104 : CNF.NClause := [(33,false),(79,false),(87,false),(64,true),(69,false)]
theorem der_78104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78104 :=
  CNF.rup_sound cl_78104 [cl_52464,cl_45655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52464 v h) (hints_cons _ _ _ (der_45655 v h) (by intro d hd; cases hd)))
def cl_78105 : CNF.NClause := [(33,false),(2,false),(87,false),(84,true),(74,false)]
theorem der_78105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78105 :=
  CNF.rup_sound cl_78105 [cl_52465,cl_77114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52465 v h) (hints_cons _ _ _ (der_77114 v h) (by intro d hd; cases hd)))
def cl_78107 : CNF.NClause := [(33,false),(87,false),(2,false),(64,false),(74,true)]
theorem der_78107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78107 :=
  CNF.rup_sound cl_78107 [cl_33358,cl_77114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33358 v h) (hints_cons _ _ _ (der_77114 v h) (by intro d hd; cases hd)))
def cl_78109 : CNF.NClause := [(33,false),(87,true),(84,false),(74,false),(79,false)]
theorem der_78109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78109 :=
  CNF.rup_sound cl_78109 [cl_52468,cl_77122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52468 v h) (hints_cons _ _ _ (der_77122 v h) (by intro d hd; cases hd)))
def cl_78110 : CNF.NClause := [(33,false),(79,false),(64,true),(84,false),(69,false)]
theorem der_78110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78110 :=
  CNF.rup_sound cl_78110 [cl_33378,cl_77117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33378 v h) (hints_cons _ _ _ (der_77117 v h) (by intro d hd; cases hd)))
def cl_78112 : CNF.NClause := [(33,false),(74,true),(79,false),(84,false),(64,false)]
theorem der_78112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78112 :=
  CNF.rup_sound cl_78112 [cl_52470,cl_77124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52470 v h) (hints_cons _ _ _ (der_77124 v h) (by intro d hd; cases hd)))
def cl_78113 : CNF.NClause := [(33,false),(2,false),(64,false),(84,true),(79,false)]
theorem der_78113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78113 :=
  CNF.rup_sound cl_78113 [cl_52472,cl_77120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52472 v h) (hints_cons _ _ _ (der_77120 v h) (by intro d hd; cases hd)))
def cl_78114 : CNF.NClause := [(33,false),(74,false),(84,true),(64,false),(69,false)]
theorem der_78114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78114 :=
  CNF.rup_sound cl_78114 [cl_33403,cl_77125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33403 v h) (hints_cons _ _ _ (der_77125 v h) (by intro d hd; cases hd)))
def cl_78115 : CNF.NClause := [(33,false),(2,false),(64,true),(69,false),(79,false)]
theorem der_78115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78115 :=
  CNF.rup_sound cl_78115 [cl_52473,cl_78110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52473 v h) (hints_cons _ _ _ (der_78110 v h) (by intro d hd; cases hd)))
def cl_78116 : CNF.NClause := [(33,false),(87,true),(84,true),(69,false),(74,false)]
theorem der_78116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78116 :=
  CNF.rup_sound cl_78116 [cl_52474,cl_78114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52474 v h) (hints_cons _ _ _ (der_78114 v h) (by intro d hd; cases hd)))
def cl_78121 : CNF.NClause := [(38,false),(73,true),(7,false),(89,false),(82,false)]
theorem der_78121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78121 :=
  CNF.rup_sound cl_78121 [cl_52478,cl_77442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52478 v h) (hints_cons _ _ _ (der_77442 v h) (by intro d hd; cases hd)))
def cl_78122 : CNF.NClause := [(38,false),(71,true),(82,false),(64,true),(89,false)]
theorem der_78122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78122 :=
  CNF.rup_sound cl_78122 [cl_52479,cl_77442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52479 v h) (hints_cons _ _ _ (der_77442 v h) (by intro d hd; cases hd)))
def cl_78123 : CNF.NClause := [(38,false),(80,false),(64,true),(82,false),(89,false)]
theorem der_78123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78123 :=
  CNF.rup_sound cl_78123 [cl_33435,cl_51141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33435 v h) (hints_cons _ _ _ (der_51141 v h) (by intro d hd; cases hd)))
def cl_78127 : CNF.NClause := [(38,false),(64,true),(89,false),(71,false),(80,false)]
theorem der_78127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78127 :=
  CNF.rup_sound cl_78127 [cl_52487,cl_51133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52487 v h) (hints_cons _ _ _ (der_51133 v h) (by intro d hd; cases hd)))
def cl_78128 : CNF.NClause := [(38,false),(7,false),(73,false),(89,false),(71,true)]
theorem der_78128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78128 :=
  CNF.rup_sound cl_78128 [cl_33445,cl_51134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33445 v h) (hints_cons _ _ _ (der_51134 v h) (by intro d hd; cases hd)))
def cl_78129 : CNF.NClause := [(38,false),(73,true),(89,false),(80,false),(71,false)]
theorem der_78129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78129 :=
  CNF.rup_sound cl_78129 [cl_33448,cl_51133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33448 v h) (hints_cons _ _ _ (der_51133 v h) (by intro d hd; cases hd)))
def cl_78131 : CNF.NClause := [(38,false),(82,true),(89,false),(73,true),(80,false)]
theorem der_78131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78131 :=
  CNF.rup_sound cl_78131 [cl_33451,cl_78129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33451 v h) (hints_cons _ _ _ (der_78129 v h) (by intro d hd; cases hd)))
def cl_78132 : CNF.NClause := [(38,false),(71,false),(80,true),(64,false),(89,false)]
theorem der_78132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78132 :=
  CNF.rup_sound cl_78132 [cl_52492,cl_77442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52492 v h) (hints_cons _ _ _ (der_77442 v h) (by intro d hd; cases hd)))
def cl_78133 : CNF.NClause := [(38,false),(7,false),(73,false),(89,false),(80,true)]
theorem der_78133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78133 :=
  CNF.rup_sound cl_78133 [cl_33452,cl_78128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33452 v h) (hints_cons _ _ _ (der_78128 v h) (by intro d hd; cases hd)))
def cl_78134 : CNF.NClause := [(38,false),(71,false),(7,true),(64,true),(89,false)]
theorem der_78134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78134 :=
  CNF.rup_sound cl_78134 [cl_52493,cl_77132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52493 v h) (hints_cons _ _ _ (der_77132 v h) (by intro d hd; cases hd)))
def cl_78137 : CNF.NClause := [(38,false),(73,true),(89,false),(7,false),(71,false)]
theorem der_78137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78137 :=
  CNF.rup_sound cl_78137 [cl_33457,cl_77136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33457 v h) (hints_cons _ _ _ (der_77136 v h) (by intro d hd; cases hd)))
def cl_78138 : CNF.NClause := [(38,false),(80,true),(89,false),(7,false),(64,false)]
theorem der_78138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78138 :=
  CNF.rup_sound cl_78138 [cl_33461,cl_52491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33461 v h) (hints_cons _ _ _ (der_52491 v h) (by intro d hd; cases hd)))
def cl_78139 : CNF.NClause := [(82,true),(38,false),(7,true),(64,false),(71,true)]
theorem der_78139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78139 :=
  CNF.rup_sound cl_78139 [cl_33462,cl_51155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33462 v h) (hints_cons _ _ _ (der_51155 v h) (by intro d hd; cases hd)))
def cl_78140 : CNF.NClause := [(38,false),(71,true),(64,true),(89,false),(80,true)]
theorem der_78140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78140 :=
  CNF.rup_sound cl_78140 [cl_33464,cl_77442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33464 v h) (hints_cons _ _ _ (der_77442 v h) (by intro d hd; cases hd)))
def cl_78141 : CNF.NClause := [(38,false),(82,false),(71,true),(80,false),(73,false)]
theorem der_78141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78141 :=
  CNF.rup_sound cl_78141 [cl_52497,cl_77133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52497 v h) (hints_cons _ _ _ (der_77133 v h) (by intro d hd; cases hd)))
def cl_78142 : CNF.NClause := [(38,false),(7,true),(82,false),(71,false),(64,false)]
theorem der_78142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78142 :=
  CNF.rup_sound cl_78142 [cl_33475,cl_51146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33475 v h) (hints_cons _ _ _ (der_51146 v h) (by intro d hd; cases hd)))
def cl_78144 : CNF.NClause := [(38,false),(82,false),(71,false),(73,true),(7,false)]
theorem der_78144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78144 :=
  CNF.rup_sound cl_78144 [cl_33482,cl_51145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33482 v h) (hints_cons _ _ _ (der_51145 v h) (by intro d hd; cases hd)))
def cl_78146 : CNF.NClause := [(38,false),(7,true),(71,true),(82,false),(89,true)]
theorem der_78146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78146 :=
  CNF.rup_sound cl_78146 [cl_33487,cl_51157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33487 v h) (hints_cons _ _ _ (der_51157 v h) (by intro d hd; cases hd)))
def cl_78148 : CNF.NClause := [(38,false),(80,false),(64,false),(73,false),(71,true)]
theorem der_78148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78148 :=
  CNF.rup_sound cl_78148 [cl_33491,cl_78141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33491 v h) (hints_cons _ _ _ (der_78141 v h) (by intro d hd; cases hd)))
def cl_78149 : CNF.NClause := [(38,false),(82,true),(7,false),(64,false),(80,false)]
theorem der_78149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78149 :=
  CNF.rup_sound cl_78149 [cl_52503,cl_51151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52503 v h) (hints_cons _ _ _ (der_51151 v h) (by intro d hd; cases hd)))
def cl_78150 : CNF.NClause := [(38,false),(7,true),(71,false),(80,false),(64,false)]
theorem der_78150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78150 :=
  CNF.rup_sound cl_78150 [cl_33494,cl_67158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33494 v h) (hints_cons _ _ _ (der_67158 v h) (by intro d hd; cases hd)))
def cl_78151 : CNF.NClause := [(38,false),(80,true),(7,true),(71,false),(64,false)]
theorem der_78151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78151 :=
  CNF.rup_sound cl_78151 [cl_52505,cl_78132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52505 v h) (hints_cons _ _ _ (der_78132 v h) (by intro d hd; cases hd)))
def cl_78152 : CNF.NClause := [(38,false),(89,true),(7,false),(71,false),(64,true)]
theorem der_78152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78152 :=
  CNF.rup_sound cl_78152 [cl_33500,cl_77136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33500 v h) (hints_cons _ _ _ (der_77136 v h) (by intro d hd; cases hd)))
def cl_78153 : CNF.NClause := [(38,false),(82,true),(7,true),(71,false),(73,false)]
theorem der_78153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78153 :=
  CNF.rup_sound cl_78153 [cl_33501,cl_67158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33501 v h) (hints_cons _ _ _ (der_67158 v h) (by intro d hd; cases hd)))
def cl_78154 : CNF.NClause := [(38,false),(80,true),(64,false),(73,true),(71,false)]
theorem der_78154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78154 :=
  CNF.rup_sound cl_78154 [cl_33506,cl_78151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33506 v h) (hints_cons _ _ _ (der_78151 v h) (by intro d hd; cases hd)))
def cl_78155 : CNF.NClause := [(38,false),(89,true),(80,true),(64,true),(7,true)]
theorem der_78155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78155 :=
  CNF.rup_sound cl_78155 [cl_52506,cl_77441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52506 v h) (hints_cons _ _ _ (der_77441 v h) (by intro d hd; cases hd)))
def cl_78156 : CNF.NClause := [(59,false),(62,true),(90,false),(73,false),(84,false)]
theorem der_78156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78156 :=
  CNF.rup_sound cl_78156 [cl_52507,cl_51183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52507 v h) (hints_cons _ _ _ (der_51183 v h) (by intro d hd; cases hd)))
def cl_78157 : CNF.NClause := [(62,true),(59,false),(90,false),(28,false),(84,false)]
theorem der_78157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78157 :=
  CNF.rup_sound cl_78157 [cl_52511,cl_51186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52511 v h) (hints_cons _ _ _ (der_51186 v h) (by intro d hd; cases hd)))
def cl_78158 : CNF.NClause := [(59,false),(84,false),(90,false),(73,false),(81,true)]
theorem der_78158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78158 :=
  CNF.rup_sound cl_78158 [cl_52514,cl_77141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52514 v h) (hints_cons _ _ _ (der_77141 v h) (by intro d hd; cases hd)))
def cl_78159 : CNF.NClause := [(59,false),(70,true),(84,false),(90,false),(28,false)]
theorem der_78159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78159 :=
  CNF.rup_sound cl_78159 [cl_52515,cl_51161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52515 v h) (hints_cons _ _ _ (der_51161 v h) (by intro d hd; cases hd)))
def cl_78161 : CNF.NClause := [(59,false),(62,false),(73,true),(90,false),(84,false)]
theorem der_78161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78161 :=
  CNF.rup_sound cl_78161 [cl_33522,cl_51161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33522 v h) (hints_cons _ _ _ (der_51161 v h) (by intro d hd; cases hd)))
def cl_78163 : CNF.NClause := [(59,false),(84,false),(81,true),(90,false),(73,true)]
theorem der_78163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78163 :=
  CNF.rup_sound cl_78163 [cl_33524,cl_51161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33524 v h) (hints_cons _ _ _ (der_51161 v h) (by intro d hd; cases hd)))
def cl_78164 : CNF.NClause := [(59,false),(84,true),(62,false),(81,false),(90,false)]
theorem der_78164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78164 :=
  CNF.rup_sound cl_78164 [cl_52518,cl_77139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52518 v h) (hints_cons _ _ _ (der_77139 v h) (by intro d hd; cases hd)))
def cl_78165 : CNF.NClause := [(59,false),(62,false),(73,true),(81,false),(90,false)]
theorem der_78165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78165 :=
  CNF.rup_sound cl_78165 [cl_33533,cl_77139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33533 v h) (hints_cons _ _ _ (der_77139 v h) (by intro d hd; cases hd)))
def cl_78167 : CNF.NClause := [(59,false),(84,true),(90,false),(81,false),(73,true)]
theorem der_78167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78167 :=
  CNF.rup_sound cl_78167 [cl_33535,cl_77137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33535 v h) (hints_cons _ _ _ (der_77137 v h) (by intro d hd; cases hd)))
def cl_78168 : CNF.NClause := [(59,false),(81,true),(62,false),(90,false),(28,false)]
theorem der_78168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78168 :=
  CNF.rup_sound cl_78168 [cl_52521,cl_77139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52521 v h) (hints_cons _ _ _ (der_77139 v h) (by intro d hd; cases hd)))
def cl_78171 : CNF.NClause := [(59,false),(81,true),(90,false),(62,false),(28,true)]
theorem der_78171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78171 :=
  CNF.rup_sound cl_78171 [cl_33548,cl_77139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33548 v h) (hints_cons _ _ _ (der_77139 v h) (by intro d hd; cases hd)))
def cl_78172 : CNF.NClause := [(59,false),(62,true),(84,false),(28,true),(73,false)]
theorem der_78172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78172 :=
  CNF.rup_sound cl_78172 [cl_33559,cl_51183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33559 v h) (hints_cons _ _ _ (der_51183 v h) (by intro d hd; cases hd)))
def cl_78173 : CNF.NClause := [(59,false),(73,true),(81,false),(28,false),(84,false)]
theorem der_78173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78173 :=
  CNF.rup_sound cl_78173 [cl_52522,cl_51180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52522 v h) (hints_cons _ _ _ (der_51180 v h) (by intro d hd; cases hd)))
def cl_78174 : CNF.NClause := [(59,false),(81,true),(84,false),(73,false),(70,false)]
theorem der_78174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78174 :=
  CNF.rup_sound cl_78174 [cl_52523,cl_77143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52523 v h) (hints_cons _ _ _ (der_77143 v h) (by intro d hd; cases hd)))
def cl_78175 : CNF.NClause := [(59,false),(73,true),(28,false),(62,false),(84,false)]
theorem der_78175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78175 :=
  CNF.rup_sound cl_78175 [cl_33572,cl_51185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33572 v h) (hints_cons _ _ _ (der_51185 v h) (by intro d hd; cases hd)))
def cl_78176 : CNF.NClause := [(73,true),(84,false),(28,false),(59,false),(70,false)]
theorem der_78176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78176 :=
  CNF.rup_sound cl_78176 [cl_33574,cl_78173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33574 v h) (hints_cons _ _ _ (der_78173 v h) (by intro d hd; cases hd)))
def cl_78177 : CNF.NClause := [(59,false),(81,true),(28,true),(84,false),(62,false)]
theorem der_78177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78177 :=
  CNF.rup_sound cl_78177 [cl_52524,cl_78171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52524 v h) (hints_cons _ _ _ (der_78171 v h) (by intro d hd; cases hd)))
def cl_78178 : CNF.NClause := [(59,false),(62,true),(28,true),(84,false),(90,true)]
theorem der_78178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78178 :=
  CNF.rup_sound cl_78178 [cl_33577,cl_78172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33577 v h) (hints_cons _ _ _ (der_78172 v h) (by intro d hd; cases hd)))
def cl_78180 : CNF.NClause := [(59,false),(81,false),(62,false),(84,true),(73,false)]
theorem der_78180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78180 :=
  CNF.rup_sound cl_78180 [cl_33578,cl_77142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33578 v h) (hints_cons _ _ _ (der_77142 v h) (by intro d hd; cases hd)))
def cl_78181 : CNF.NClause := [(59,false),(73,true),(81,false),(62,false),(28,false)]
theorem der_78181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78181 :=
  CNF.rup_sound cl_78181 [cl_33584,cl_77142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33584 v h) (hints_cons _ _ _ (der_77142 v h) (by intro d hd; cases hd)))
def cl_78183 : CNF.NClause := [(59,false),(62,true),(84,true),(73,true),(81,false)]
theorem der_78183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78183 :=
  CNF.rup_sound cl_78183 [cl_52526,cl_78167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52526 v h) (hints_cons _ _ _ (der_78167 v h) (by intro d hd; cases hd)))
def cl_78184 : CNF.NClause := [(59,false),(84,true),(90,true),(28,false),(73,false)]
theorem der_78184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78184 :=
  CNF.rup_sound cl_78184 [cl_52527,cl_51198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52527 v h) (hints_cons _ _ _ (der_51198 v h) (by intro d hd; cases hd)))
def cl_78186 : CNF.NClause := [(59,false),(81,true),(62,false),(84,true),(28,true)]
theorem der_78186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78186 :=
  CNF.rup_sound cl_78186 [cl_52528,cl_78171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52528 v h) (hints_cons _ _ _ (der_78171 v h) (by intro d hd; cases hd)))
def cl_78189 : CNF.NClause := [(41,false),(75,true),(76,false),(72,false),(92,false)]
theorem der_78189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78189 :=
  CNF.rup_sound cl_78189 [cl_52534,cl_51219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52534 v h) (hints_cons _ _ _ (der_51219 v h) (by intro d hd; cases hd)))
def cl_78192 : CNF.NClause := [(10,false),(41,false),(76,false),(74,true),(72,false)]
theorem der_78192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78192 :=
  CNF.rup_sound cl_78192 [cl_52538,cl_51236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52538 v h) (hints_cons _ _ _ (der_51236 v h) (by intro d hd; cases hd)))
def cl_78194 : CNF.NClause := [(41,false),(74,true),(92,false),(72,false),(75,false)]
theorem der_78194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78194 :=
  CNF.rup_sound cl_78194 [cl_33629,cl_51224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33629 v h) (hints_cons _ _ _ (der_51224 v h) (by intro d hd; cases hd)))
def cl_78195 : CNF.NClause := [(41,false),(10,false),(73,false),(74,true),(75,false)]
theorem der_78195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78195 :=
  CNF.rup_sound cl_78195 [cl_52540,cl_77152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52540 v h) (hints_cons _ _ _ (der_77152 v h) (by intro d hd; cases hd)))
def cl_78196 : CNF.NClause := [(41,false),(92,false),(74,true),(75,false),(10,false)]
theorem der_78196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78196 :=
  CNF.rup_sound cl_78196 [cl_33633,cl_78194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33633 v h) (hints_cons _ _ _ (der_78194 v h) (by intro d hd; cases hd)))
def cl_78198 : CNF.NClause := [(41,false),(75,true),(73,false),(72,false),(92,false)]
theorem der_78198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78198 :=
  CNF.rup_sound cl_78198 [cl_33635,cl_51229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33635 v h) (hints_cons _ _ _ (der_51229 v h) (by intro d hd; cases hd)))
def cl_78199 : CNF.NClause := [(41,false),(75,true),(74,false),(10,false),(92,false)]
theorem der_78199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78199 :=
  CNF.rup_sound cl_78199 [cl_33636,cl_51262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33636 v h) (hints_cons _ _ _ (der_51262 v h) (by intro d hd; cases hd)))
def cl_78201 : CNF.NClause := [(41,false),(74,false),(76,true),(72,true),(92,false)]
theorem der_78201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78201 :=
  CNF.rup_sound cl_78201 [cl_33640,cl_77154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33640 v h) (hints_cons _ _ _ (der_77154 v h) (by intro d hd; cases hd)))
def cl_78202 : CNF.NClause := [(41,false),(75,true),(73,false),(92,false),(10,false)]
theorem der_78202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78202 :=
  CNF.rup_sound cl_78202 [cl_33641,cl_77156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33641 v h) (hints_cons _ _ _ (der_77156 v h) (by intro d hd; cases hd)))
def cl_78205 : CNF.NClause := [(41,false),(92,true),(73,false),(75,false),(76,false)]
theorem der_78205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78205 :=
  CNF.rup_sound cl_78205 [cl_52543,cl_77471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52543 v h) (hints_cons _ _ _ (der_77471 v h) (by intro d hd; cases hd)))
def cl_78207 : CNF.NClause := [(41,false),(72,true),(75,false),(76,false),(10,false)]
theorem der_78207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78207 :=
  CNF.rup_sound cl_78207 [cl_33651,cl_77152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33651 v h) (hints_cons _ _ _ (der_77152 v h) (by intro d hd; cases hd)))
def cl_78210 : CNF.NClause := [(41,false),(75,true),(76,false),(73,false),(10,false)]
theorem der_78210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78210 :=
  CNF.rup_sound cl_78210 [cl_33667,cl_77156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33667 v h) (hints_cons _ _ _ (der_77156 v h) (by intro d hd; cases hd)))
def cl_78211 : CNF.NClause := [(41,false),(75,true),(72,false),(76,false),(73,false)]
theorem der_78211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78211 :=
  CNF.rup_sound cl_78211 [cl_33668,cl_78189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33668 v h) (hints_cons _ _ _ (der_78189 v h) (by intro d hd; cases hd)))
def cl_78212 : CNF.NClause := [(41,false),(75,true),(76,false),(92,true),(73,false)]
theorem der_78212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78212 :=
  CNF.rup_sound cl_78212 [cl_33670,cl_78210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33670 v h) (hints_cons _ _ _ (der_78210 v h) (by intro d hd; cases hd)))
def cl_78213 : CNF.NClause := [(73,true),(72,true),(74,true),(76,false),(41,false)]
theorem der_78213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78213 :=
  CNF.rup_sound cl_78213 [cl_33674,cl_77151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33674 v h) (hints_cons _ _ _ (der_77151 v h) (by intro d hd; cases hd)))
def cl_78214 : CNF.NClause := [(41,false),(73,false),(74,false),(76,true),(75,false)]
theorem der_78214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78214 :=
  CNF.rup_sound cl_78214 [cl_33675,cl_77154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33675 v h) (hints_cons _ _ _ (der_77154 v h) (by intro d hd; cases hd)))
def cl_78217 : CNF.NClause := [(41,false),(10,false),(76,true),(92,true),(73,false)]
theorem der_78217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78217 :=
  CNF.rup_sound cl_78217 [cl_52547,cl_77156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52547 v h) (hints_cons _ _ _ (der_77156 v h) (by intro d hd; cases hd)))
def cl_78219 : CNF.NClause := [(41,false),(74,true),(73,false),(92,true),(76,true)]
theorem der_78219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78219 :=
  CNF.rup_sound cl_78219 [cl_33698,cl_51265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33698 v h) (hints_cons _ _ _ (der_51265 v h) (by intro d hd; cases hd)))
def cl_78224 : CNF.NClause := [(35,false),(87,false),(83,false),(68,true),(73,false)]
theorem der_78224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78224 :=
  CNF.rup_sound cl_78224 [cl_33715,cl_51272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33715 v h) (hints_cons _ _ _ (der_51272 v h) (by intro d hd; cases hd)))
def cl_78228 : CNF.NClause := [(35,false),(87,false),(63,false),(83,true),(78,false)]
theorem der_78228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78228 :=
  CNF.rup_sound cl_78228 [cl_49170,cl_51278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49170 v h) (hints_cons _ _ _ (der_51278 v h) (by intro d hd; cases hd)))
def cl_78231 : CNF.NClause := [(35,false),(87,false),(78,true),(63,false),(73,false)]
theorem der_78231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78231 :=
  CNF.rup_sound cl_78231 [cl_33734,cl_51282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33734 v h) (hints_cons _ _ _ (der_51282 v h) (by intro d hd; cases hd)))
def cl_78233 : CNF.NClause := [(35,false),(87,false),(83,true),(73,true),(68,true)]
theorem der_78233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78233 :=
  CNF.rup_sound cl_78233 [cl_52553,cl_77158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52553 v h) (hints_cons _ _ _ (der_77158 v h) (by intro d hd; cases hd)))
def cl_78234 : CNF.NClause := [(35,false),(4,true),(68,false),(78,false),(83,false)]
theorem der_78234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78234 :=
  CNF.rup_sound cl_78234 [cl_33748,cl_51297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33748 v h) (hints_cons _ _ _ (der_51297 v h) (by intro d hd; cases hd)))
def cl_78235 : CNF.NClause := [(35,false),(63,true),(83,false),(68,false),(78,false)]
theorem der_78235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78235 :=
  CNF.rup_sound cl_78235 [cl_33749,cl_51293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33749 v h) (hints_cons _ _ _ (der_51293 v h) (by intro d hd; cases hd)))
def cl_78236 : CNF.NClause := [(35,false),(68,true),(63,false),(73,false),(78,false)]
theorem der_78236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78236 :=
  CNF.rup_sound cl_78236 [cl_33750,cl_51307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33750 v h) (hints_cons _ _ _ (der_51307 v h) (by intro d hd; cases hd)))
def cl_78237 : CNF.NClause := [(35,false),(4,false),(68,true),(83,false),(73,false)]
theorem der_78237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78237 :=
  CNF.rup_sound cl_78237 [cl_33751,cl_51295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33751 v h) (hints_cons _ _ _ (der_51295 v h) (by intro d hd; cases hd)))
def cl_78238 : CNF.NClause := [(35,false),(63,true),(83,false),(4,true),(78,false)]
theorem der_78238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78238 :=
  CNF.rup_sound cl_78238 [cl_33752,cl_51293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33752 v h) (hints_cons _ _ _ (der_51293 v h) (by intro d hd; cases hd)))
def cl_78241 : CNF.NClause := [(35,false),(4,true),(73,true),(83,false),(78,false)]
theorem der_78241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78241 :=
  CNF.rup_sound cl_78241 [cl_52556,cl_77158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52556 v h) (hints_cons _ _ _ (der_77158 v h) (by intro d hd; cases hd)))
def cl_78244 : CNF.NClause := [(35,false),(78,true),(73,false),(83,false),(63,false)]
theorem der_78244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78244 :=
  CNF.rup_sound cl_78244 [cl_33762,cl_78231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33762 v h) (hints_cons _ _ _ (der_78231 v h) (by intro d hd; cases hd)))
def cl_78245 : CNF.NClause := [(35,false),(4,false),(63,false),(78,true),(83,false)]
theorem der_78245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78245 :=
  CNF.rup_sound cl_78245 [cl_52558,cl_51298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52558 v h) (hints_cons _ _ _ (der_51298 v h) (by intro d hd; cases hd)))
def cl_78247 : CNF.NClause := [(35,false),(63,true),(4,false),(83,false),(68,false)]
theorem der_78247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78247 :=
  CNF.rup_sound cl_78247 [cl_33766,cl_78235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33766 v h) (hints_cons _ _ _ (der_78235 v h) (by intro d hd; cases hd)))
def cl_78248 : CNF.NClause := [(35,false),(83,false),(78,true),(63,true),(68,true)]
theorem der_78248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78248 :=
  CNF.rup_sound cl_78248 [cl_33771,cl_77157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33771 v h) (hints_cons _ _ _ (der_77157 v h) (by intro d hd; cases hd)))
def cl_78249 : CNF.NClause := [(35,false),(73,false),(63,false),(78,false),(83,true)]
theorem der_78249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78249 :=
  CNF.rup_sound cl_78249 [cl_33775,cl_78228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33775 v h) (hints_cons _ _ _ (der_78228 v h) (by intro d hd; cases hd)))
def cl_78250 : CNF.NClause := [(35,false),(4,true),(78,false),(83,true),(73,false)]
theorem der_78250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78250 :=
  CNF.rup_sound cl_78250 [cl_33777,cl_59959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33777 v h) (hints_cons _ _ _ (der_59959 v h) (by intro d hd; cases hd)))
def cl_78251 : CNF.NClause := [(35,false),(63,true),(78,false),(68,false),(4,false)]
theorem der_78251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78251 :=
  CNF.rup_sound cl_78251 [cl_33780,cl_78235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33780 v h) (hints_cons _ _ _ (der_78235 v h) (by intro d hd; cases hd)))
def cl_78252 : CNF.NClause := [(35,false),(63,true),(87,true),(4,false),(78,false)]
theorem der_78252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78252 :=
  CNF.rup_sound cl_78252 [cl_52561,cl_77163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52561 v h) (hints_cons _ _ _ (der_77163 v h) (by intro d hd; cases hd)))
def cl_78254 : CNF.NClause := [(35,false),(4,true),(78,true),(73,false),(68,false)]
theorem der_78254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78254 :=
  CNF.rup_sound cl_78254 [cl_33784,cl_77164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33784 v h) (hints_cons _ _ _ (der_77164 v h) (by intro d hd; cases hd)))
def cl_78255 : CNF.NClause := [(35,false),(87,true),(73,false),(4,false),(83,true)]
theorem der_78255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78255 :=
  CNF.rup_sound cl_78255 [cl_33787,cl_77163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33787 v h) (hints_cons _ _ _ (der_77163 v h) (by intro d hd; cases hd)))
def cl_78256 : CNF.NClause := [(35,false),(63,true),(83,true),(78,true),(68,false)]
theorem der_78256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78256 :=
  CNF.rup_sound cl_78256 [cl_33794,cl_77159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33794 v h) (hints_cons _ _ _ (der_77159 v h) (by intro d hd; cases hd)))
def cl_78257 : CNF.NClause := [(35,false),(83,true),(63,true),(73,true),(68,true)]
theorem der_78257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78257 :=
  CNF.rup_sound cl_78257 [cl_52563,cl_78233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52563 v h) (hints_cons _ _ _ (der_78233 v h) (by intro d hd; cases hd)))
def cl_78261 : CNF.NClause := [(57,false),(62,true),(75,false),(91,false),(71,false)]
theorem der_78261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78261 :=
  CNF.rup_sound cl_78261 [cl_52565,cl_60012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52565 v h) (hints_cons _ _ _ (der_60012 v h) (by intro d hd; cases hd)))
def cl_78272 : CNF.NClause := [(57,false),(75,true),(91,false),(83,true),(62,true)]
theorem der_78272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78272 :=
  CNF.rup_sound cl_78272 [cl_33838,cl_77167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33838 v h) (hints_cons _ _ _ (der_77167 v h) (by intro d hd; cases hd)))
def cl_78273 : CNF.NClause := [(57,false),(79,true),(75,false),(83,false),(71,false)]
theorem der_78273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78273 :=
  CNF.rup_sound cl_78273 [cl_52577,cl_77172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52577 v h) (hints_cons _ _ _ (der_77172 v h) (by intro d hd; cases hd)))
def cl_78277 : CNF.NClause := [(57,false),(26,false),(75,false),(62,false),(83,true)]
theorem der_78277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78277 :=
  CNF.rup_sound cl_78277 [cl_33875,cl_51364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33875 v h) (hints_cons _ _ _ (der_51364 v h) (by intro d hd; cases hd)))
def cl_78278 : CNF.NClause := [(57,false),(62,false),(79,true),(71,false),(75,false)]
theorem der_78278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78278 :=
  CNF.rup_sound cl_78278 [cl_33876,cl_78273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33876 v h) (hints_cons _ _ _ (der_78273 v h) (by intro d hd; cases hd)))
def cl_78279 : CNF.NClause := [(57,false),(71,false),(26,false),(62,false),(79,true)]
theorem der_78279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78279 :=
  CNF.rup_sound cl_78279 [cl_33882,cl_78278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33882 v h) (hints_cons _ _ _ (der_78278 v h) (by intro d hd; cases hd)))
def cl_78280 : CNF.NClause := [(57,false),(26,true),(83,true),(71,false),(91,true)]
theorem der_78280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78280 :=
  CNF.rup_sound cl_78280 [cl_52578,cl_77177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52578 v h) (hints_cons _ _ _ (der_77177 v h) (by intro d hd; cases hd)))
def cl_78281 : CNF.NClause := [(57,false),(26,true),(83,true),(75,true),(91,true)]
theorem der_78281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78281 :=
  CNF.rup_sound cl_78281 [cl_33887,cl_78280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33887 v h) (hints_cons _ _ _ (der_78280 v h) (by intro d hd; cases hd)))
def cl_78283 : CNF.NClause := [(51,false),(68,true),(71,false),(70,false),(92,false)]
theorem der_78283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78283 :=
  CNF.rup_sound cl_78283 [cl_33890,cl_51371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33890 v h) (hints_cons _ _ _ (der_51371 v h) (by intro d hd; cases hd)))
def cl_78288 : CNF.NClause := [(51,false),(92,false),(69,false),(67,true),(70,false)]
theorem der_78288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78288 :=
  CNF.rup_sound cl_78288 [cl_33902,cl_51377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33902 v h) (hints_cons _ _ _ (der_51377 v h) (by intro d hd; cases hd)))
def cl_78289 : CNF.NClause := [(51,false),(20,false),(68,false),(70,true),(67,false)]
theorem der_78289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78289 :=
  CNF.rup_sound cl_78289 [cl_52588,cl_77195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52588 v h) (hints_cons _ _ _ (der_77195 v h) (by intro d hd; cases hd)))
def cl_78290 : CNF.NClause := [(51,false),(92,false),(70,true),(68,false),(67,false)]
theorem der_78290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78290 :=
  CNF.rup_sound cl_78290 [cl_33912,cl_77189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33912 v h) (hints_cons _ _ _ (der_77189 v h) (by intro d hd; cases hd)))
def cl_78295 : CNF.NClause := [(51,false),(92,false),(71,true),(69,true),(67,true)]
theorem der_78295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78295 :=
  CNF.rup_sound cl_78295 [cl_33926,cl_77189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33926 v h) (hints_cons _ _ _ (der_77189 v h) (by intro d hd; cases hd)))
def cl_78297 : CNF.NClause := [(51,false),(67,true),(70,false),(69,false),(71,false)]
theorem der_78297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78297 :=
  CNF.rup_sound cl_78297 [cl_33927,cl_77192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33927 v h) (hints_cons _ _ _ (der_77192 v h) (by intro d hd; cases hd)))
def cl_78298 : CNF.NClause := [(51,false),(20,true),(71,false),(69,false),(70,false)]
theorem der_78298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78298 :=
  CNF.rup_sound cl_78298 [cl_33928,cl_51390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33928 v h) (hints_cons _ _ _ (der_51390 v h) (by intro d hd; cases hd)))
def cl_78301 : CNF.NClause := [(51,false),(69,true),(70,false),(71,false),(68,false)]
theorem der_78301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78301 :=
  CNF.rup_sound cl_78301 [cl_52594,cl_51402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52594 v h) (hints_cons _ _ _ (der_51402 v h) (by intro d hd; cases hd)))
def cl_78303 : CNF.NClause := [(51,false),(20,true),(68,false),(69,false),(71,false)]
theorem der_78303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78303 :=
  CNF.rup_sound cl_78303 [cl_33939,cl_78298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33939 v h) (hints_cons _ _ _ (der_78298 v h) (by intro d hd; cases hd)))
def cl_78306 : CNF.NClause := [(51,false),(20,false),(69,false),(68,true),(71,false)]
theorem der_78306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78306 :=
  CNF.rup_sound cl_78306 [cl_33942,cl_52592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33942 v h) (hints_cons _ _ _ (der_52592 v h) (by intro d hd; cases hd)))
def cl_78307 : CNF.NClause := [(51,false),(70,true),(67,true),(71,false),(69,true)]
theorem der_78307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78307 :=
  CNF.rup_sound cl_78307 [cl_33946,cl_77192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33946 v h) (hints_cons _ _ _ (der_77192 v h) (by intro d hd; cases hd)))
def cl_78309 : CNF.NClause := [(51,false),(69,true),(71,false),(70,true),(67,false)]
theorem der_78309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78309 :=
  CNF.rup_sound cl_78309 [cl_33948,cl_77195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33948 v h) (hints_cons _ _ _ (der_77195 v h) (by intro d hd; cases hd)))
def cl_78310 : CNF.NClause := [(20,false),(51,false),(71,true),(70,false),(68,false)]
theorem der_78310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78310 :=
  CNF.rup_sound cl_78310 [cl_52596,cl_51402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52596 v h) (hints_cons _ _ _ (der_51402 v h) (by intro d hd; cases hd)))
def cl_78311 : CNF.NClause := [(51,false),(68,false),(67,false),(71,true),(70,false)]
theorem der_78311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78311 :=
  CNF.rup_sound cl_78311 [cl_33951,cl_51401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33951 v h) (hints_cons _ _ _ (der_51401 v h) (by intro d hd; cases hd)))
def cl_78315 : CNF.NClause := [(51,false),(71,true),(68,false),(67,true),(70,false)]
theorem der_78315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78315 :=
  CNF.rup_sound cl_78315 [cl_33961,cl_78310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33961 v h) (hints_cons _ _ _ (der_78310 v h) (by intro d hd; cases hd)))
def cl_78317 : CNF.NClause := [(51,false),(92,true),(70,false),(20,true),(71,true)]
theorem der_78317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78317 :=
  CNF.rup_sound cl_78317 [cl_33964,cl_51413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33964 v h) (hints_cons _ _ _ (der_51413 v h) (by intro d hd; cases hd)))
def cl_78318 : CNF.NClause := [(51,false),(20,false),(68,false),(71,true),(67,false)]
theorem der_78318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78318 :=
  CNF.rup_sound cl_78318 [cl_33965,cl_77195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33965 v h) (hints_cons _ _ _ (der_77195 v h) (by intro d hd; cases hd)))
def cl_78321 : CNF.NClause := [(51,false),(92,true),(20,true),(71,true),(68,false)]
theorem der_78321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78321 :=
  CNF.rup_sound cl_78321 [cl_33976,cl_51413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33976 v h) (hints_cons _ _ _ (der_51413 v h) (by intro d hd; cases hd)))
def cl_78322 : CNF.NClause := [(51,false),(69,true),(67,true),(68,true),(70,true)]
theorem der_78322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78322 :=
  CNF.rup_sound cl_78322 [cl_33980,cl_77192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33980 v h) (hints_cons _ _ _ (der_77192 v h) (by intro d hd; cases hd)))
def cl_78323 : CNF.NClause := [(50,false),(74,true),(77,false),(85,false),(90,false)]
theorem der_78323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78323 :=
  CNF.rup_sound cl_78323 [cl_52599,cl_51416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52599 v h) (hints_cons _ _ _ (der_51416 v h) (by intro d hd; cases hd)))
def cl_78325 : CNF.NClause := [(50,false),(63,true),(19,false),(85,false),(74,false)]
theorem der_78325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78325 :=
  CNF.rup_sound cl_78325 [cl_52601,cl_77204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52601 v h) (hints_cons _ _ _ (der_77204 v h) (by intro d hd; cases hd)))
def cl_78327 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(90,false)]
theorem der_78327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78327 :=
  CNF.rup_sound cl_78327 [cl_52602,cl_77198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52602 v h) (hints_cons _ _ _ (der_77198 v h) (by intro d hd; cases hd)))
def cl_78328 : CNF.NClause := [(50,false),(19,true),(63,false),(85,false),(90,false)]
theorem der_78328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78328 :=
  CNF.rup_sound cl_78328 [cl_33988,cl_77198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33988 v h) (hints_cons _ _ _ (der_77198 v h) (by intro d hd; cases hd)))
def cl_78329 : CNF.NClause := [(50,false),(71,true),(90,false),(85,false),(63,false)]
theorem der_78329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78329 :=
  CNF.rup_sound cl_78329 [cl_33994,cl_78328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33994 v h) (hints_cons _ _ _ (der_78328 v h) (by intro d hd; cases hd)))
def cl_78331 : CNF.NClause := [(50,false),(19,false),(77,false),(90,false),(85,true)]
theorem der_78331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78331 :=
  CNF.rup_sound cl_78331 [cl_52604,cl_51423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52604 v h) (hints_cons _ _ _ (der_51423 v h) (by intro d hd; cases hd)))
def cl_78335 : CNF.NClause := [(50,false),(19,false),(85,true),(63,false),(90,false)]
theorem der_78335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78335 :=
  CNF.rup_sound cl_78335 [cl_52605,cl_77198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52605 v h) (hints_cons _ _ _ (der_77198 v h) (by intro d hd; cases hd)))
def cl_78336 : CNF.NClause := [(50,false),(63,true),(19,false),(77,true),(90,false)]
theorem der_78336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78336 :=
  CNF.rup_sound cl_78336 [cl_52606,cl_51433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52606 v h) (hints_cons _ _ _ (der_51433 v h) (by intro d hd; cases hd)))
def cl_78341 : CNF.NClause := [(74,true),(50,false),(19,false),(77,false),(85,false)]
theorem der_78341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_78341 :=
  CNF.rup_sound cl_78341 [cl_52609,cl_78323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52609 v h) (hints_cons _ _ _ (der_78323 v h) (by intro d hd; cases hd)))
def chunk076 : List CNF.NClause := [cl_77527,cl_77529,cl_77530,cl_77531,cl_77533,cl_77534,cl_77535,cl_77536,cl_77537,cl_77538,cl_77539,cl_77540,cl_77541,cl_77542,cl_77543,cl_77544,cl_77546,cl_77547,cl_77549,cl_77550,cl_77551,cl_77554,cl_77556,cl_77560,cl_77561,cl_77563,cl_77565,cl_77567,cl_77568,cl_77571,cl_77573,cl_77574,cl_77575,cl_77578,cl_77581,cl_77582,cl_77583,cl_77585,cl_77587,cl_77594,cl_77597,cl_77598,cl_77601,cl_77603,cl_77606,cl_77610,cl_77611,cl_77612,cl_77614,cl_77616,cl_77618,cl_77619,cl_77620,cl_77621,cl_77623,cl_77625,cl_77626,cl_77627,cl_77628,cl_77629,cl_77631,cl_77632,cl_77633,cl_77635,cl_77636,cl_77637,cl_77639,cl_77640,cl_77641,cl_77643,cl_77644,cl_77645,cl_77646,cl_77649,cl_77650,cl_77651,cl_77652,cl_77655,cl_77656,cl_77657,cl_77659,cl_77660,cl_77661,cl_77662,cl_77663,cl_77664,cl_77665,cl_77667,cl_77668,cl_77669,cl_77670,cl_77671,cl_77673,cl_77674,cl_77675,cl_77676,cl_77677,cl_77678,cl_77680,cl_77682,cl_77683,cl_77693,cl_77694,cl_77696,cl_77697,cl_77698,cl_77700,cl_77701,cl_77702,cl_77705,cl_77707,cl_77708,cl_77711,cl_77712,cl_77715,cl_77718,cl_77721,cl_77722,cl_77723,cl_77725,cl_77726,cl_77728,cl_77729,cl_77730,cl_77731,cl_77732,cl_77734,cl_77735,cl_77736,cl_77737,cl_77738,cl_77739,cl_77740,cl_77741,cl_77743,cl_77744,cl_77745,cl_77746,cl_77748,cl_77749,cl_77750,cl_77751,cl_77753,cl_77754,cl_77756,cl_77759,cl_77760,cl_77762,cl_77763,cl_77764,cl_77765,cl_77768,cl_77769,cl_77770,cl_77772,cl_77773,cl_77776,cl_77777,cl_77778,cl_77780,cl_77782,cl_77786,cl_77787,cl_77788,cl_77790,cl_77791,cl_77792,cl_77793,cl_77794,cl_77795,cl_77796,cl_77797,cl_77798,cl_77799,cl_77805,cl_77806,cl_77807,cl_77808,cl_77809,cl_77811,cl_77817,cl_77818,cl_77819,cl_77820,cl_77822,cl_77828,cl_77829,cl_77830,cl_77831,cl_77832,cl_77833,cl_77834,cl_77836,cl_77837,cl_77838,cl_77839,cl_77840,cl_77841,cl_77843,cl_77844,cl_77846,cl_77848,cl_77850,cl_77851,cl_77852,cl_77854,cl_77855,cl_77857,cl_77858,cl_77859,cl_77860,cl_77861,cl_77862,cl_77863,cl_77864,cl_77866,cl_77867,cl_77870,cl_77871,cl_77872,cl_77876,cl_77877,cl_77879,cl_77880,cl_77881,cl_77882,cl_77883,cl_77884,cl_77885,cl_77886,cl_77887,cl_77890,cl_77891,cl_77893,cl_77894,cl_77896,cl_77899,cl_77903,cl_77904,cl_77905,cl_77907,cl_77908,cl_77911,cl_77913,cl_77914,cl_77916,cl_77917,cl_77920,cl_77921,cl_77923,cl_77924,cl_77926,cl_77927,cl_77928,cl_77931,cl_77932,cl_77933,cl_77934,cl_77935,cl_77936,cl_77938,cl_77939,cl_77940,cl_77941,cl_77942,cl_77943,cl_77944,cl_77945,cl_77946,cl_77947,cl_77948,cl_77949,cl_77950,cl_77951,cl_77952,cl_77953,cl_77954,cl_77956,cl_77957,cl_77958,cl_77960,cl_77961,cl_77963,cl_77964,cl_77966,cl_77968,cl_77969,cl_77971,cl_77973,cl_77974,cl_77978,cl_77980,cl_77981,cl_77982,cl_77983,cl_77984,cl_77985,cl_77986,cl_77991,cl_77992,cl_77993,cl_77994,cl_77996,cl_77998,cl_78001,cl_78002,cl_78003,cl_78004,cl_78005,cl_78007,cl_78009,cl_78011,cl_78012,cl_78013,cl_78017,cl_78018,cl_78019,cl_78021,cl_78022,cl_78023,cl_78024,cl_78025,cl_78029,cl_78030,cl_78032,cl_78036,cl_78038,cl_78040,cl_78041,cl_78043,cl_78044,cl_78046,cl_78047,cl_78048,cl_78049,cl_78050,cl_78052,cl_78053,cl_78056,cl_78058,cl_78059,cl_78060,cl_78062,cl_78065,cl_78067,cl_78068,cl_78069,cl_78072,cl_78074,cl_78075,cl_78077,cl_78079,cl_78080,cl_78081,cl_78084,cl_78085,cl_78086,cl_78087,cl_78088,cl_78091,cl_78092,cl_78093,cl_78100,cl_78101,cl_78103,cl_78104,cl_78105,cl_78107,cl_78109,cl_78110,cl_78112,cl_78113,cl_78114,cl_78115,cl_78116,cl_78121,cl_78122,cl_78123,cl_78127,cl_78128,cl_78129,cl_78131,cl_78132,cl_78133,cl_78134,cl_78137,cl_78138,cl_78139,cl_78140,cl_78141,cl_78142,cl_78144,cl_78146,cl_78148,cl_78149,cl_78150,cl_78151,cl_78152,cl_78153,cl_78154,cl_78155,cl_78156,cl_78157,cl_78158,cl_78159,cl_78161,cl_78163,cl_78164,cl_78165,cl_78167,cl_78168,cl_78171,cl_78172,cl_78173,cl_78174,cl_78175,cl_78176,cl_78177,cl_78178,cl_78180,cl_78181,cl_78183,cl_78184,cl_78186,cl_78189,cl_78192,cl_78194,cl_78195,cl_78196,cl_78198,cl_78199,cl_78201,cl_78202,cl_78205,cl_78207,cl_78210,cl_78211,cl_78212,cl_78213,cl_78214,cl_78217,cl_78219,cl_78224,cl_78228,cl_78231,cl_78233,cl_78234,cl_78235,cl_78236,cl_78237,cl_78238,cl_78241,cl_78244,cl_78245,cl_78247,cl_78248,cl_78249,cl_78250,cl_78251,cl_78252,cl_78254,cl_78255,cl_78256,cl_78257,cl_78261,cl_78272,cl_78273,cl_78277,cl_78278,cl_78279,cl_78280,cl_78281,cl_78283,cl_78288,cl_78289,cl_78290,cl_78295,cl_78297,cl_78298,cl_78301,cl_78303,cl_78306,cl_78307,cl_78309,cl_78310,cl_78311,cl_78315,cl_78317,cl_78318,cl_78321,cl_78322,cl_78323,cl_78325,cl_78327,cl_78328,cl_78329,cl_78331,cl_78335,cl_78336,cl_78341]
theorem chunk_sound076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk076, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_77527 v h) (hints_cons _ _ _ (der_77529 v h) (hints_cons _ _ _ (der_77530 v h) (hints_cons _ _ _ (der_77531 v h) (hints_cons _ _ _ (der_77533 v h) (hints_cons _ _ _ (der_77534 v h) (hints_cons _ _ _ (der_77535 v h) (hints_cons _ _ _ (der_77536 v h) (hints_cons _ _ _ (der_77537 v h) (hints_cons _ _ _ (der_77538 v h) (hints_cons _ _ _ (der_77539 v h) (hints_cons _ _ _ (der_77540 v h) (hints_cons _ _ _ (der_77541 v h) (hints_cons _ _ _ (der_77542 v h) (hints_cons _ _ _ (der_77543 v h) (hints_cons _ _ _ (der_77544 v h) (hints_cons _ _ _ (der_77546 v h) (hints_cons _ _ _ (der_77547 v h) (hints_cons _ _ _ (der_77549 v h) (hints_cons _ _ _ (der_77550 v h) (hints_cons _ _ _ (der_77551 v h) (hints_cons _ _ _ (der_77554 v h) (hints_cons _ _ _ (der_77556 v h) (hints_cons _ _ _ (der_77560 v h) (hints_cons _ _ _ (der_77561 v h) (hints_cons _ _ _ (der_77563 v h) (hints_cons _ _ _ (der_77565 v h) (hints_cons _ _ _ (der_77567 v h) (hints_cons _ _ _ (der_77568 v h) (hints_cons _ _ _ (der_77571 v h) (hints_cons _ _ _ (der_77573 v h) (hints_cons _ _ _ (der_77574 v h) (hints_cons _ _ _ (der_77575 v h) (hints_cons _ _ _ (der_77578 v h) (hints_cons _ _ _ (der_77581 v h) (hints_cons _ _ _ (der_77582 v h) (hints_cons _ _ _ (der_77583 v h) (hints_cons _ _ _ (der_77585 v h) (hints_cons _ _ _ (der_77587 v h) (hints_cons _ _ _ (der_77594 v h) (hints_cons _ _ _ (der_77597 v h) (hints_cons _ _ _ (der_77598 v h) (hints_cons _ _ _ (der_77601 v h) (hints_cons _ _ _ (der_77603 v h) (hints_cons _ _ _ (der_77606 v h) (hints_cons _ _ _ (der_77610 v h) (hints_cons _ _ _ (der_77611 v h) (hints_cons _ _ _ (der_77612 v h) (hints_cons _ _ _ (der_77614 v h) (hints_cons _ _ _ (der_77616 v h) (hints_cons _ _ _ (der_77618 v h) (hints_cons _ _ _ (der_77619 v h) (hints_cons _ _ _ (der_77620 v h) (hints_cons _ _ _ (der_77621 v h) (hints_cons _ _ _ (der_77623 v h) (hints_cons _ _ _ (der_77625 v h) (hints_cons _ _ _ (der_77626 v h) (hints_cons _ _ _ (der_77627 v h) (hints_cons _ _ _ (der_77628 v h) (hints_cons _ _ _ (der_77629 v h) (hints_cons _ _ _ (der_77631 v h) (hints_cons _ _ _ (der_77632 v h) (hints_cons _ _ _ (der_77633 v h) (hints_cons _ _ _ (der_77635 v h) (hints_cons _ _ _ (der_77636 v h) (hints_cons _ _ _ (der_77637 v h) (hints_cons _ _ _ (der_77639 v h) (hints_cons _ _ _ (der_77640 v h) (hints_cons _ _ _ (der_77641 v h) (hints_cons _ _ _ (der_77643 v h) (hints_cons _ _ _ (der_77644 v h) (hints_cons _ _ _ (der_77645 v h) (hints_cons _ _ _ (der_77646 v h) (hints_cons _ _ _ (der_77649 v h) (hints_cons _ _ _ (der_77650 v h) (hints_cons _ _ _ (der_77651 v h) (hints_cons _ _ _ (der_77652 v h) (hints_cons _ _ _ (der_77655 v h) (hints_cons _ _ _ (der_77656 v h) (hints_cons _ _ _ (der_77657 v h) (hints_cons _ _ _ (der_77659 v h) (hints_cons _ _ _ (der_77660 v h) (hints_cons _ _ _ (der_77661 v h) (hints_cons _ _ _ (der_77662 v h) (hints_cons _ _ _ (der_77663 v h) (hints_cons _ _ _ (der_77664 v h) (hints_cons _ _ _ (der_77665 v h) (hints_cons _ _ _ (der_77667 v h) (hints_cons _ _ _ (der_77668 v h) (hints_cons _ _ _ (der_77669 v h) (hints_cons _ _ _ (der_77670 v h) (hints_cons _ _ _ (der_77671 v h) (hints_cons _ _ _ (der_77673 v h) (hints_cons _ _ _ (der_77674 v h) (hints_cons _ _ _ (der_77675 v h) (hints_cons _ _ _ (der_77676 v h) (hints_cons _ _ _ (der_77677 v h) (hints_cons _ _ _ (der_77678 v h) (hints_cons _ _ _ (der_77680 v h) (hints_cons _ _ _ (der_77682 v h) (hints_cons _ _ _ (der_77683 v h) (hints_cons _ _ _ (der_77693 v h) (hints_cons _ _ _ (der_77694 v h) (hints_cons _ _ _ (der_77696 v h) (hints_cons _ _ _ (der_77697 v h) (hints_cons _ _ _ (der_77698 v h) (hints_cons _ _ _ (der_77700 v h) (hints_cons _ _ _ (der_77701 v h) (hints_cons _ _ _ (der_77702 v h) (hints_cons _ _ _ (der_77705 v h) (hints_cons _ _ _ (der_77707 v h) (hints_cons _ _ _ (der_77708 v h) (hints_cons _ _ _ (der_77711 v h) (hints_cons _ _ _ (der_77712 v h) (hints_cons _ _ _ (der_77715 v h) (hints_cons _ _ _ (der_77718 v h) (hints_cons _ _ _ (der_77721 v h) (hints_cons _ _ _ (der_77722 v h) (hints_cons _ _ _ (der_77723 v h) (hints_cons _ _ _ (der_77725 v h) (hints_cons _ _ _ (der_77726 v h) (hints_cons _ _ _ (der_77728 v h) (hints_cons _ _ _ (der_77729 v h) (hints_cons _ _ _ (der_77730 v h) (hints_cons _ _ _ (der_77731 v h) (hints_cons _ _ _ (der_77732 v h) (hints_cons _ _ _ (der_77734 v h) (hints_cons _ _ _ (der_77735 v h) (hints_cons _ _ _ (der_77736 v h) (hints_cons _ _ _ (der_77737 v h) (hints_cons _ _ _ (der_77738 v h) (hints_cons _ _ _ (der_77739 v h) (hints_cons _ _ _ (der_77740 v h) (hints_cons _ _ _ (der_77741 v h) (hints_cons _ _ _ (der_77743 v h) (hints_cons _ _ _ (der_77744 v h) (hints_cons _ _ _ (der_77745 v h) (hints_cons _ _ _ (der_77746 v h) (hints_cons _ _ _ (der_77748 v h) (hints_cons _ _ _ (der_77749 v h) (hints_cons _ _ _ (der_77750 v h) (hints_cons _ _ _ (der_77751 v h) (hints_cons _ _ _ (der_77753 v h) (hints_cons _ _ _ (der_77754 v h) (hints_cons _ _ _ (der_77756 v h) (hints_cons _ _ _ (der_77759 v h) (hints_cons _ _ _ (der_77760 v h) (hints_cons _ _ _ (der_77762 v h) (hints_cons _ _ _ (der_77763 v h) (hints_cons _ _ _ (der_77764 v h) (hints_cons _ _ _ (der_77765 v h) (hints_cons _ _ _ (der_77768 v h) (hints_cons _ _ _ (der_77769 v h) (hints_cons _ _ _ (der_77770 v h) (hints_cons _ _ _ (der_77772 v h) (hints_cons _ _ _ (der_77773 v h) (hints_cons _ _ _ (der_77776 v h) (hints_cons _ _ _ (der_77777 v h) (hints_cons _ _ _ (der_77778 v h) (hints_cons _ _ _ (der_77780 v h) (hints_cons _ _ _ (der_77782 v h) (hints_cons _ _ _ (der_77786 v h) (hints_cons _ _ _ (der_77787 v h) (hints_cons _ _ _ (der_77788 v h) (hints_cons _ _ _ (der_77790 v h) (hints_cons _ _ _ (der_77791 v h) (hints_cons _ _ _ (der_77792 v h) (hints_cons _ _ _ (der_77793 v h) (hints_cons _ _ _ (der_77794 v h) (hints_cons _ _ _ (der_77795 v h) (hints_cons _ _ _ (der_77796 v h) (hints_cons _ _ _ (der_77797 v h) (hints_cons _ _ _ (der_77798 v h) (hints_cons _ _ _ (der_77799 v h) (hints_cons _ _ _ (der_77805 v h) (hints_cons _ _ _ (der_77806 v h) (hints_cons _ _ _ (der_77807 v h) (hints_cons _ _ _ (der_77808 v h) (hints_cons _ _ _ (der_77809 v h) (hints_cons _ _ _ (der_77811 v h) (hints_cons _ _ _ (der_77817 v h) (hints_cons _ _ _ (der_77818 v h) (hints_cons _ _ _ (der_77819 v h) (hints_cons _ _ _ (der_77820 v h) (hints_cons _ _ _ (der_77822 v h) (hints_cons _ _ _ (der_77828 v h) (hints_cons _ _ _ (der_77829 v h) (hints_cons _ _ _ (der_77830 v h) (hints_cons _ _ _ (der_77831 v h) (hints_cons _ _ _ (der_77832 v h) (hints_cons _ _ _ (der_77833 v h) (hints_cons _ _ _ (der_77834 v h) (hints_cons _ _ _ (der_77836 v h) (hints_cons _ _ _ (der_77837 v h) (hints_cons _ _ _ (der_77838 v h) (hints_cons _ _ _ (der_77839 v h) (hints_cons _ _ _ (der_77840 v h) (hints_cons _ _ _ (der_77841 v h) (hints_cons _ _ _ (der_77843 v h) (hints_cons _ _ _ (der_77844 v h) (hints_cons _ _ _ (der_77846 v h) (hints_cons _ _ _ (der_77848 v h) (hints_cons _ _ _ (der_77850 v h) (hints_cons _ _ _ (der_77851 v h) (hints_cons _ _ _ (der_77852 v h) (hints_cons _ _ _ (der_77854 v h) (hints_cons _ _ _ (der_77855 v h) (hints_cons _ _ _ (der_77857 v h) (hints_cons _ _ _ (der_77858 v h) (hints_cons _ _ _ (der_77859 v h) (hints_cons _ _ _ (der_77860 v h) (hints_cons _ _ _ (der_77861 v h) (hints_cons _ _ _ (der_77862 v h) (hints_cons _ _ _ (der_77863 v h) (hints_cons _ _ _ (der_77864 v h) (hints_cons _ _ _ (der_77866 v h) (hints_cons _ _ _ (der_77867 v h) (hints_cons _ _ _ (der_77870 v h) (hints_cons _ _ _ (der_77871 v h) (hints_cons _ _ _ (der_77872 v h) (hints_cons _ _ _ (der_77876 v h) (hints_cons _ _ _ (der_77877 v h) (hints_cons _ _ _ (der_77879 v h) (hints_cons _ _ _ (der_77880 v h) (hints_cons _ _ _ (der_77881 v h) (hints_cons _ _ _ (der_77882 v h) (hints_cons _ _ _ (der_77883 v h) (hints_cons _ _ _ (der_77884 v h) (hints_cons _ _ _ (der_77885 v h) (hints_cons _ _ _ (der_77886 v h) (hints_cons _ _ _ (der_77887 v h) (hints_cons _ _ _ (der_77890 v h) (hints_cons _ _ _ (der_77891 v h) (hints_cons _ _ _ (der_77893 v h) (hints_cons _ _ _ (der_77894 v h) (hints_cons _ _ _ (der_77896 v h) (hints_cons _ _ _ (der_77899 v h) (hints_cons _ _ _ (der_77903 v h) (hints_cons _ _ _ (der_77904 v h) (hints_cons _ _ _ (der_77905 v h) (hints_cons _ _ _ (der_77907 v h) (hints_cons _ _ _ (der_77908 v h) (hints_cons _ _ _ (der_77911 v h) (hints_cons _ _ _ (der_77913 v h) (hints_cons _ _ _ (der_77914 v h) (hints_cons _ _ _ (der_77916 v h) (hints_cons _ _ _ (der_77917 v h) (hints_cons _ _ _ (der_77920 v h) (hints_cons _ _ _ (der_77921 v h) (hints_cons _ _ _ (der_77923 v h) (hints_cons _ _ _ (der_77924 v h) (hints_cons _ _ _ (der_77926 v h) (hints_cons _ _ _ (der_77927 v h) (hints_cons _ _ _ (der_77928 v h) (hints_cons _ _ _ (der_77931 v h) (hints_cons _ _ _ (der_77932 v h) (hints_cons _ _ _ (der_77933 v h) (hints_cons _ _ _ (der_77934 v h) (hints_cons _ _ _ (der_77935 v h) (hints_cons _ _ _ (der_77936 v h) (hints_cons _ _ _ (der_77938 v h) (hints_cons _ _ _ (der_77939 v h) (hints_cons _ _ _ (der_77940 v h) (hints_cons _ _ _ (der_77941 v h) (hints_cons _ _ _ (der_77942 v h) (hints_cons _ _ _ (der_77943 v h) (hints_cons _ _ _ (der_77944 v h) (hints_cons _ _ _ (der_77945 v h) (hints_cons _ _ _ (der_77946 v h) (hints_cons _ _ _ (der_77947 v h) (hints_cons _ _ _ (der_77948 v h) (hints_cons _ _ _ (der_77949 v h) (hints_cons _ _ _ (der_77950 v h) (hints_cons _ _ _ (der_77951 v h) (hints_cons _ _ _ (der_77952 v h) (hints_cons _ _ _ (der_77953 v h) (hints_cons _ _ _ (der_77954 v h) (hints_cons _ _ _ (der_77956 v h) (hints_cons _ _ _ (der_77957 v h) (hints_cons _ _ _ (der_77958 v h) (hints_cons _ _ _ (der_77960 v h) (hints_cons _ _ _ (der_77961 v h) (hints_cons _ _ _ (der_77963 v h) (hints_cons _ _ _ (der_77964 v h) (hints_cons _ _ _ (der_77966 v h) (hints_cons _ _ _ (der_77968 v h) (hints_cons _ _ _ (der_77969 v h) (hints_cons _ _ _ (der_77971 v h) (hints_cons _ _ _ (der_77973 v h) (hints_cons _ _ _ (der_77974 v h) (hints_cons _ _ _ (der_77978 v h) (hints_cons _ _ _ (der_77980 v h) (hints_cons _ _ _ (der_77981 v h) (hints_cons _ _ _ (der_77982 v h) (hints_cons _ _ _ (der_77983 v h) (hints_cons _ _ _ (der_77984 v h) (hints_cons _ _ _ (der_77985 v h) (hints_cons _ _ _ (der_77986 v h) (hints_cons _ _ _ (der_77991 v h) (hints_cons _ _ _ (der_77992 v h) (hints_cons _ _ _ (der_77993 v h) (hints_cons _ _ _ (der_77994 v h) (hints_cons _ _ _ (der_77996 v h) (hints_cons _ _ _ (der_77998 v h) (hints_cons _ _ _ (der_78001 v h) (hints_cons _ _ _ (der_78002 v h) (hints_cons _ _ _ (der_78003 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_78005 v h) (hints_cons _ _ _ (der_78007 v h) (hints_cons _ _ _ (der_78009 v h) (hints_cons _ _ _ (der_78011 v h) (hints_cons _ _ _ (der_78012 v h) (hints_cons _ _ _ (der_78013 v h) (hints_cons _ _ _ (der_78017 v h) (hints_cons _ _ _ (der_78018 v h) (hints_cons _ _ _ (der_78019 v h) (hints_cons _ _ _ (der_78021 v h) (hints_cons _ _ _ (der_78022 v h) (hints_cons _ _ _ (der_78023 v h) (hints_cons _ _ _ (der_78024 v h) (hints_cons _ _ _ (der_78025 v h) (hints_cons _ _ _ (der_78029 v h) (hints_cons _ _ _ (der_78030 v h) (hints_cons _ _ _ (der_78032 v h) (hints_cons _ _ _ (der_78036 v h) (hints_cons _ _ _ (der_78038 v h) (hints_cons _ _ _ (der_78040 v h) (hints_cons _ _ _ (der_78041 v h) (hints_cons _ _ _ (der_78043 v h) (hints_cons _ _ _ (der_78044 v h) (hints_cons _ _ _ (der_78046 v h) (hints_cons _ _ _ (der_78047 v h) (hints_cons _ _ _ (der_78048 v h) (hints_cons _ _ _ (der_78049 v h) (hints_cons _ _ _ (der_78050 v h) (hints_cons _ _ _ (der_78052 v h) (hints_cons _ _ _ (der_78053 v h) (hints_cons _ _ _ (der_78056 v h) (hints_cons _ _ _ (der_78058 v h) (hints_cons _ _ _ (der_78059 v h) (hints_cons _ _ _ (der_78060 v h) (hints_cons _ _ _ (der_78062 v h) (hints_cons _ _ _ (der_78065 v h) (hints_cons _ _ _ (der_78067 v h) (hints_cons _ _ _ (der_78068 v h) (hints_cons _ _ _ (der_78069 v h) (hints_cons _ _ _ (der_78072 v h) (hints_cons _ _ _ (der_78074 v h) (hints_cons _ _ _ (der_78075 v h) (hints_cons _ _ _ (der_78077 v h) (hints_cons _ _ _ (der_78079 v h) (hints_cons _ _ _ (der_78080 v h) (hints_cons _ _ _ (der_78081 v h) (hints_cons _ _ _ (der_78084 v h) (hints_cons _ _ _ (der_78085 v h) (hints_cons _ _ _ (der_78086 v h) (hints_cons _ _ _ (der_78087 v h) (hints_cons _ _ _ (der_78088 v h) (hints_cons _ _ _ (der_78091 v h) (hints_cons _ _ _ (der_78092 v h) (hints_cons _ _ _ (der_78093 v h) (hints_cons _ _ _ (der_78100 v h) (hints_cons _ _ _ (der_78101 v h) (hints_cons _ _ _ (der_78103 v h) (hints_cons _ _ _ (der_78104 v h) (hints_cons _ _ _ (der_78105 v h) (hints_cons _ _ _ (der_78107 v h) (hints_cons _ _ _ (der_78109 v h) (hints_cons _ _ _ (der_78110 v h) (hints_cons _ _ _ (der_78112 v h) (hints_cons _ _ _ (der_78113 v h) (hints_cons _ _ _ (der_78114 v h) (hints_cons _ _ _ (der_78115 v h) (hints_cons _ _ _ (der_78116 v h) (hints_cons _ _ _ (der_78121 v h) (hints_cons _ _ _ (der_78122 v h) (hints_cons _ _ _ (der_78123 v h) (hints_cons _ _ _ (der_78127 v h) (hints_cons _ _ _ (der_78128 v h) (hints_cons _ _ _ (der_78129 v h) (hints_cons _ _ _ (der_78131 v h) (hints_cons _ _ _ (der_78132 v h) (hints_cons _ _ _ (der_78133 v h) (hints_cons _ _ _ (der_78134 v h) (hints_cons _ _ _ (der_78137 v h) (hints_cons _ _ _ (der_78138 v h) (hints_cons _ _ _ (der_78139 v h) (hints_cons _ _ _ (der_78140 v h) (hints_cons _ _ _ (der_78141 v h) (hints_cons _ _ _ (der_78142 v h) (hints_cons _ _ _ (der_78144 v h) (hints_cons _ _ _ (der_78146 v h) (hints_cons _ _ _ (der_78148 v h) (hints_cons _ _ _ (der_78149 v h) (hints_cons _ _ _ (der_78150 v h) (hints_cons _ _ _ (der_78151 v h) (hints_cons _ _ _ (der_78152 v h) (hints_cons _ _ _ (der_78153 v h) (hints_cons _ _ _ (der_78154 v h) (hints_cons _ _ _ (der_78155 v h) (hints_cons _ _ _ (der_78156 v h) (hints_cons _ _ _ (der_78157 v h) (hints_cons _ _ _ (der_78158 v h) (hints_cons _ _ _ (der_78159 v h) (hints_cons _ _ _ (der_78161 v h) (hints_cons _ _ _ (der_78163 v h) (hints_cons _ _ _ (der_78164 v h) (hints_cons _ _ _ (der_78165 v h) (hints_cons _ _ _ (der_78167 v h) (hints_cons _ _ _ (der_78168 v h) (hints_cons _ _ _ (der_78171 v h) (hints_cons _ _ _ (der_78172 v h) (hints_cons _ _ _ (der_78173 v h) (hints_cons _ _ _ (der_78174 v h) (hints_cons _ _ _ (der_78175 v h) (hints_cons _ _ _ (der_78176 v h) (hints_cons _ _ _ (der_78177 v h) (hints_cons _ _ _ (der_78178 v h) (hints_cons _ _ _ (der_78180 v h) (hints_cons _ _ _ (der_78181 v h) (hints_cons _ _ _ (der_78183 v h) (hints_cons _ _ _ (der_78184 v h) (hints_cons _ _ _ (der_78186 v h) (hints_cons _ _ _ (der_78189 v h) (hints_cons _ _ _ (der_78192 v h) (hints_cons _ _ _ (der_78194 v h) (hints_cons _ _ _ (der_78195 v h) (hints_cons _ _ _ (der_78196 v h) (hints_cons _ _ _ (der_78198 v h) (hints_cons _ _ _ (der_78199 v h) (hints_cons _ _ _ (der_78201 v h) (hints_cons _ _ _ (der_78202 v h) (hints_cons _ _ _ (der_78205 v h) (hints_cons _ _ _ (der_78207 v h) (hints_cons _ _ _ (der_78210 v h) (hints_cons _ _ _ (der_78211 v h) (hints_cons _ _ _ (der_78212 v h) (hints_cons _ _ _ (der_78213 v h) (hints_cons _ _ _ (der_78214 v h) (hints_cons _ _ _ (der_78217 v h) (hints_cons _ _ _ (der_78219 v h) (hints_cons _ _ _ (der_78224 v h) (hints_cons _ _ _ (der_78228 v h) (hints_cons _ _ _ (der_78231 v h) (hints_cons _ _ _ (der_78233 v h) (hints_cons _ _ _ (der_78234 v h) (hints_cons _ _ _ (der_78235 v h) (hints_cons _ _ _ (der_78236 v h) (hints_cons _ _ _ (der_78237 v h) (hints_cons _ _ _ (der_78238 v h) (hints_cons _ _ _ (der_78241 v h) (hints_cons _ _ _ (der_78244 v h) (hints_cons _ _ _ (der_78245 v h) (hints_cons _ _ _ (der_78247 v h) (hints_cons _ _ _ (der_78248 v h) (hints_cons _ _ _ (der_78249 v h) (hints_cons _ _ _ (der_78250 v h) (hints_cons _ _ _ (der_78251 v h) (hints_cons _ _ _ (der_78252 v h) (hints_cons _ _ _ (der_78254 v h) (hints_cons _ _ _ (der_78255 v h) (hints_cons _ _ _ (der_78256 v h) (hints_cons _ _ _ (der_78257 v h) (hints_cons _ _ _ (der_78261 v h) (hints_cons _ _ _ (der_78272 v h) (hints_cons _ _ _ (der_78273 v h) (hints_cons _ _ _ (der_78277 v h) (hints_cons _ _ _ (der_78278 v h) (hints_cons _ _ _ (der_78279 v h) (hints_cons _ _ _ (der_78280 v h) (hints_cons _ _ _ (der_78281 v h) (hints_cons _ _ _ (der_78283 v h) (hints_cons _ _ _ (der_78288 v h) (hints_cons _ _ _ (der_78289 v h) (hints_cons _ _ _ (der_78290 v h) (hints_cons _ _ _ (der_78295 v h) (hints_cons _ _ _ (der_78297 v h) (hints_cons _ _ _ (der_78298 v h) (hints_cons _ _ _ (der_78301 v h) (hints_cons _ _ _ (der_78303 v h) (hints_cons _ _ _ (der_78306 v h) (hints_cons _ _ _ (der_78307 v h) (hints_cons _ _ _ (der_78309 v h) (hints_cons _ _ _ (der_78310 v h) (hints_cons _ _ _ (der_78311 v h) (hints_cons _ _ _ (der_78315 v h) (hints_cons _ _ _ (der_78317 v h) (hints_cons _ _ _ (der_78318 v h) (hints_cons _ _ _ (der_78321 v h) (hints_cons _ _ _ (der_78322 v h) (hints_cons _ _ _ (der_78323 v h) (hints_cons _ _ _ (der_78325 v h) (hints_cons _ _ _ (der_78327 v h) (hints_cons _ _ _ (der_78328 v h) (hints_cons _ _ _ (der_78329 v h) (hints_cons _ _ _ (der_78331 v h) (hints_cons _ _ _ (der_78335 v h) (hints_cons _ _ _ (der_78336 v h) (hints_cons _ _ _ (der_78341 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix076 := prefix075 ++ chunk076
theorem prefix_sound076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix076, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound075 v h c hc
  · exact chunk_sound076 v h c hc
end Percolation.NReplay
