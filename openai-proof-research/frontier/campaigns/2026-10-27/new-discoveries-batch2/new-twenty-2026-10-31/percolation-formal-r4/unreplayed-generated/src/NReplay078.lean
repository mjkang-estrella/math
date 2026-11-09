import NReplay077
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_79476 : CNF.NClause := [(81,true),(82,false),(40,false)]
theorem der_79476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79476 :=
  CNF.rup_sound cl_79476 [cl_77076,cl_50845,cl_77077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77076 v h) (hints_cons _ _ _ (der_50845 v h) (hints_cons _ _ _ (der_77077 v h) (by intro d hd; cases hd))))
def cl_79477 : CNF.NClause := [(33,false),(84,false),(74,true)]
theorem der_79477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79477 :=
  CNF.rup_sound cl_79477 [cl_77119,cl_77111,cl_51109,cl_78112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77119 v h) (hints_cons _ _ _ (der_77111 v h) (hints_cons _ _ _ (der_51109 v h) (hints_cons _ _ _ (der_78112 v h) (by intro d hd; cases hd)))))
def cl_79478 : CNF.NClause := [(69,true),(33,false),(74,true)]
theorem der_79478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79478 :=
  CNF.rup_sound cl_79478 [cl_50544,cl_77131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50544 v h) (hints_cons _ _ _ (der_77131 v h) (by intro d hd; cases hd)))
def cl_79480 : CNF.NClause := [(78,true),(73,false),(35,false)]
theorem der_79480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79480 :=
  CNF.rup_sound cl_79480 [cl_77164,cl_78244,cl_51307,cl_78231,cl_78255,cl_78254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77164 v h) (hints_cons _ _ _ (der_78244 v h) (hints_cons _ _ _ (der_51307 v h) (hints_cons _ _ _ (der_78231 v h) (hints_cons _ _ _ (der_78255 v h) (hints_cons _ _ _ (der_78254 v h) (by intro d hd; cases hd)))))))
def cl_79481 : CNF.NClause := [(8,false),(79,true),(39,false)]
theorem der_79481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79481 :=
  CNF.rup_sound cl_79481 [cl_77042,cl_76541,cl_15880,cl_76540,cl_15891,cl_37816,cl_15868,cl_54421,cl_15887,cl_76784,cl_15881,cl_12724,cl_49808,cl_15879,cl_49884,cl_15889,cl_49807,cl_15884,cl_29848,cl_15869,cl_15670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77042 v h) (hints_cons _ _ _ (der_76541 v h) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_76540 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_37816 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_54421 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_76784 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (inp_12724 v h) (hints_cons _ _ _ (der_49808 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_49884 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_49807 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_29848 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_15670 v h) (by intro d hd; cases hd))))))))))))))))))))))
def cl_79482 : CNF.NClause := [(90,false),(59,false),(70,true)]
theorem der_79482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79482 :=
  CNF.rup_sound cl_79482 [cl_77141,cl_51158,cl_51162,cl_78167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77141 v h) (hints_cons _ _ _ (der_51158 v h) (hints_cons _ _ _ (der_51162 v h) (hints_cons _ _ _ (der_78167 v h) (by intro d hd; cases hd)))))
def cl_79484 : CNF.NClause := [(64,true),(85,false),(43,false)]
theorem der_79484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79484 :=
  CNF.rup_sound cl_79484 [cl_77104,cl_51037,cl_77098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77104 v h) (hints_cons _ _ _ (der_51037 v h) (hints_cons _ _ _ (der_77098 v h) (by intro d hd; cases hd))))
def cl_79485 : CNF.NClause := [(69,true),(33,false),(79,false)]
theorem der_79485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79485 :=
  CNF.rup_sound cl_79485 [cl_77122,cl_50544,cl_51092,cl_51114,cl_77120,cl_49698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77122 v h) (hints_cons _ _ _ (der_50544 v h) (hints_cons _ _ _ (der_51092 v h) (hints_cons _ _ _ (der_51114 v h) (hints_cons _ _ _ (der_77120 v h) (hints_cons _ _ _ (der_49698 v h) (by intro d hd; cases hd)))))))
def cl_79486 : CNF.NClause := [(69,true),(33,false)]
theorem der_79486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79486 :=
  CNF.rup_sound cl_79486 [cl_79478,cl_79485,cl_77127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79478 v h) (hints_cons _ _ _ (der_79485 v h) (hints_cons _ _ _ (der_77127 v h) (by intro d hd; cases hd))))
def cl_79487 : CNF.NClause := [(67,true),(54,false),(81,false)]
theorem der_79487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79487 :=
  CNF.rup_sound cl_79487 [cl_77065,cl_77762,cl_77772,cl_77756,cl_77750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77065 v h) (hints_cons _ _ _ (der_77762 v h) (hints_cons _ _ _ (der_77772 v h) (hints_cons _ _ _ (der_77756 v h) (hints_cons _ _ _ (der_77750 v h) (by intro d hd; cases hd))))))
def cl_79489 : CNF.NClause := [(21,false),(79,true),(52,false)]
theorem der_79489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79489 :=
  CNF.rup_sound cl_79489 [cl_77349,cl_49804,cl_15882,cl_54421,cl_15874,cl_76607,cl_15891,cl_76609,cl_15880,cl_76569,cl_15868,cl_42466,cl_15881,cl_12721,cl_49771,cl_15867,cl_43827,cl_15872,cl_49787,cl_15877,cl_15671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77349 v h) (hints_cons _ _ _ (der_49804 v h) (hints_cons _ _ _ (der_15882 v h) (hints_cons _ _ _ (der_54421 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_76607 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_76609 v h) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_76569 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_42466 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (inp_12721 v h) (hints_cons _ _ _ (der_49771 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_43827 v h) (hints_cons _ _ _ (der_15872 v h) (hints_cons _ _ _ (der_49787 v h) (hints_cons _ _ _ (der_15877 v h) (hints_cons _ _ _ (der_15671 v h) (by intro d hd; cases hd))))))))))))))))))))))
def cl_79491 : CNF.NClause := [(44,false),(13,true)]
theorem der_79491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79491 :=
  CNF.rup_sound cl_79491 [cl_79458,cl_79472,cl_79473,cl_78468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79458 v h) (hints_cons _ _ _ (der_79472 v h) (hints_cons _ _ _ (der_79473 v h) (hints_cons _ _ _ (der_78468 v h) (by intro d hd; cases hd)))))
def cl_79492 : CNF.NClause := [(76,false),(79,false),(39,false),(8,true)]
theorem der_79492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79492 :=
  CNF.rup_sound cl_79492 [cl_79459,cl_77603,cl_77610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79459 v h) (hints_cons _ _ _ (der_77603 v h) (hints_cons _ _ _ (der_77610 v h) (by intro d hd; cases hd))))
def cl_79493 : CNF.NClause := [(79,false),(39,false),(8,true)]
theorem der_79493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79493 :=
  CNF.rup_sound cl_79493 [cl_79492,cl_77598,cl_77618,cl_77612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79492 v h) (hints_cons _ _ _ (der_77598 v h) (hints_cons _ _ _ (der_77618 v h) (hints_cons _ _ _ (der_77612 v h) (by intro d hd; cases hd)))))
def cl_79494 : CNF.NClause := [(68,true),(39,false),(8,true)]
theorem der_79494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79494 :=
  CNF.rup_sound cl_79494 [cl_79493,cl_79459,cl_78642,cl_77616,cl_78641,cl_77618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79493 v h) (hints_cons _ _ _ (der_79459 v h) (hints_cons _ _ _ (der_78642 v h) (hints_cons _ _ _ (der_77616 v h) (hints_cons _ _ _ (der_78641 v h) (hints_cons _ _ _ (der_77618 v h) (by intro d hd; cases hd)))))))
def cl_79495 : CNF.NClause := [(39,false),(8,true)]
theorem der_79495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79495 :=
  CNF.rup_sound cl_79495 [cl_79494,cl_79493,cl_79459,cl_77041,cl_32191,cl_78641,cl_50625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79494 v h) (hints_cons _ _ _ (der_79493 v h) (hints_cons _ _ _ (der_79459 v h) (hints_cons _ _ _ (der_77041 v h) (hints_cons _ _ _ (der_32191 v h) (hints_cons _ _ _ (der_78641 v h) (hints_cons _ _ _ (der_50625 v h) (by intro d hd; cases hd))))))))
def cl_79496 : CNF.NClause := [(78,false),(58,false),(69,true),(27,true)]
theorem der_79496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79496 :=
  CNF.rup_sound cl_79496 [cl_50761,cl_77730,cl_32518,cl_77708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50761 v h) (hints_cons _ _ _ (der_77730 v h) (hints_cons _ _ _ (der_32518 v h) (hints_cons _ _ _ (der_77708 v h) (by intro d hd; cases hd)))))
def cl_79497 : CNF.NClause := [(76,false),(58,false),(69,true),(27,true)]
theorem der_79497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79497 :=
  CNF.rup_sound cl_79497 [cl_77734,cl_79496,cl_77735,cl_77722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77734 v h) (hints_cons _ _ _ (der_79496 v h) (hints_cons _ _ _ (der_77735 v h) (hints_cons _ _ _ (der_77722 v h) (by intro d hd; cases hd)))))
def cl_79498 : CNF.NClause := [(78,false),(58,false),(27,true)]
theorem der_79498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79498 :=
  CNF.rup_sound cl_79498 [cl_79496,cl_50747,cl_77726,cl_77705,cl_32535,cl_77729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79496 v h) (hints_cons _ _ _ (der_50747 v h) (hints_cons _ _ _ (der_77726 v h) (hints_cons _ _ _ (der_77705 v h) (hints_cons _ _ _ (der_32535 v h) (hints_cons _ _ _ (der_77729 v h) (by intro d hd; cases hd)))))))
def cl_79499 : CNF.NClause := [(85,false),(76,true),(58,false),(27,true)]
theorem der_79499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79499 :=
  CNF.rup_sound cl_79499 [cl_79498,cl_77725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79498 v h) (hints_cons _ _ _ (der_77725 v h) (by intro d hd; cases hd)))
def cl_79500 : CNF.NClause := [(85,false),(58,false),(27,true)]
theorem der_79500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79500 :=
  CNF.rup_sound cl_79500 [cl_79499,cl_79497,cl_79498,cl_77721,cl_50751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79499 v h) (hints_cons _ _ _ (der_79497 v h) (hints_cons _ _ _ (der_79498 v h) (hints_cons _ _ _ (der_77721 v h) (hints_cons _ _ _ (der_50751 v h) (by intro d hd; cases hd))))))
def cl_79501 : CNF.NClause := [(89,false),(58,false),(27,true)]
theorem der_79501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79501 :=
  CNF.rup_sound cl_79501 [cl_79498,cl_79500,cl_77718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79498 v h) (hints_cons _ _ _ (der_79500 v h) (hints_cons _ _ _ (der_77718 v h) (by intro d hd; cases hd))))
def cl_79502 : CNF.NClause := [(58,false),(27,true)]
theorem der_79502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79502 :=
  CNF.rup_sound cl_79502 [cl_79498,cl_79500,cl_77735,cl_79501,cl_32535,cl_79497,cl_77721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79498 v h) (hints_cons _ _ _ (der_79500 v h) (hints_cons _ _ _ (der_77735 v h) (hints_cons _ _ _ (der_79501 v h) (hints_cons _ _ _ (der_32535 v h) (hints_cons _ _ _ (der_79497 v h) (hints_cons _ _ _ (der_77721 v h) (by intro d hd; cases hd))))))))
def cl_79503 : CNF.NClause := [(86,false),(53,false),(75,false),(22,true)]
theorem der_79503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79503 :=
  CNF.rup_sound cl_79503 [cl_51877,cl_51812,cl_78521,cl_51960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51877 v h) (hints_cons _ _ _ (der_51812 v h) (hints_cons _ _ _ (der_78521 v h) (hints_cons _ _ _ (der_51960 v h) (by intro d hd; cases hd)))))
def cl_79504 : CNF.NClause := [(90,false),(53,false),(75,false),(22,true)]
theorem der_79504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79504 :=
  CNF.rup_sound cl_79504 [cl_79503,cl_78515,cl_78521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79503 v h) (hints_cons _ _ _ (der_78515 v h) (hints_cons _ _ _ (der_78521 v h) (by intro d hd; cases hd))))
def cl_79505 : CNF.NClause := [(53,false),(75,false),(22,true)]
theorem der_79505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79505 :=
  CNF.rup_sound cl_79505 [cl_79503,cl_79504,cl_51880,cl_78536,cl_34868,cl_51582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79503 v h) (hints_cons _ _ _ (der_79504 v h) (hints_cons _ _ _ (der_51880 v h) (hints_cons _ _ _ (der_78536 v h) (hints_cons _ _ _ (der_34868 v h) (hints_cons _ _ _ (der_51582 v h) (by intro d hd; cases hd)))))))
def cl_79506 : CNF.NClause := [(86,false),(53,false),(22,true)]
theorem der_79506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79506 :=
  CNF.rup_sound cl_79506 [cl_79505,cl_77380,cl_78513,cl_78523,cl_51878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79505 v h) (hints_cons _ _ _ (der_77380 v h) (hints_cons _ _ _ (der_78513 v h) (hints_cons _ _ _ (der_78523 v h) (hints_cons _ _ _ (der_51878 v h) (by intro d hd; cases hd))))))
def cl_79507 : CNF.NClause := [(91,false),(75,false),(57,false),(26,true)]
theorem der_79507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79507 :=
  CNF.rup_sound cl_79507 [cl_77683,cl_77182,cl_47772,cl_60012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77683 v h) (hints_cons _ _ _ (der_77182 v h) (hints_cons _ _ _ (der_47772 v h) (hints_cons _ _ _ (der_60012 v h) (by intro d hd; cases hd)))))
def cl_79508 : CNF.NClause := [(71,false),(57,false),(26,true)]
theorem der_79508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79508 :=
  CNF.rup_sound cl_79508 [cl_47772,cl_78280,cl_79507,cl_51335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47772 v h) (hints_cons _ _ _ (der_78280 v h) (hints_cons _ _ _ (der_79507 v h) (hints_cons _ _ _ (der_51335 v h) (by intro d hd; cases hd)))))
def cl_79509 : CNF.NClause := [(83,false),(57,false),(26,true)]
theorem der_79509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79509 :=
  CNF.rup_sound cl_79509 [cl_79508,cl_77173,cl_49554,cl_51347,cl_51352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79508 v h) (hints_cons _ _ _ (der_77173 v h) (hints_cons _ _ _ (der_49554 v h) (hints_cons _ _ _ (der_51347 v h) (hints_cons _ _ _ (der_51352 v h) (by intro d hd; cases hd))))))
def cl_79510 : CNF.NClause := [(75,true),(57,false),(26,true)]
theorem der_79510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79510 :=
  CNF.rup_sound cl_79510 [cl_79509,cl_78281,cl_79508,cl_77170,cl_78272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79509 v h) (hints_cons _ _ _ (der_78281 v h) (hints_cons _ _ _ (der_79508 v h) (hints_cons _ _ _ (der_77170 v h) (hints_cons _ _ _ (der_78272 v h) (by intro d hd; cases hd))))))
def cl_79511 : CNF.NClause := [(75,false),(84,false),(47,false),(16,true)]
theorem der_79511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79511 :=
  CNF.rup_sound cl_79511 [cl_51646,cl_79460,cl_51576,cl_40091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51646 v h) (hints_cons _ _ _ (der_79460 v h) (hints_cons _ _ _ (der_51576 v h) (hints_cons _ _ _ (der_40091 v h) (by intro d hd; cases hd)))))
def cl_79512 : CNF.NClause := [(75,false),(47,false),(16,true)]
theorem der_79512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79512 :=
  CNF.rup_sound cl_79512 [cl_79511,cl_79460,cl_78420,cl_40091,cl_51802,cl_51648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79511 v h) (hints_cons _ _ _ (der_79460 v h) (hints_cons _ _ _ (der_78420 v h) (hints_cons _ _ _ (der_40091 v h) (hints_cons _ _ _ (der_51802 v h) (hints_cons _ _ _ (der_51648 v h) (by intro d hd; cases hd)))))))
def cl_79513 : CNF.NClause := [(83,false),(36,false),(84,false),(5,true)]
theorem der_79513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79513 :=
  CNF.rup_sound cl_79513 [cl_49536,cl_50694,cl_77674,cl_50698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49536 v h) (hints_cons _ _ _ (der_50694 v h) (hints_cons _ _ _ (der_77674 v h) (hints_cons _ _ _ (der_50698 v h) (by intro d hd; cases hd)))))
def cl_79514 : CNF.NClause := [(85,false),(36,false),(86,false),(5,true)]
theorem der_79514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79514 :=
  CNF.rup_sound cl_79514 [cl_49536,cl_77646,cl_50685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49536 v h) (hints_cons _ _ _ (der_77646 v h) (hints_cons _ _ _ (der_50685 v h) (by intro d hd; cases hd))))
def cl_79515 : CNF.NClause := [(36,false),(86,false),(5,true)]
theorem der_79515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79515 :=
  CNF.rup_sound cl_79515 [cl_79514,cl_77050,cl_49536,cl_77667,cl_77649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79514 v h) (hints_cons _ _ _ (der_77050 v h) (hints_cons _ _ _ (der_49536 v h) (hints_cons _ _ _ (der_77667 v h) (hints_cons _ _ _ (der_77649 v h) (by intro d hd; cases hd))))))
def cl_79516 : CNF.NClause := [(85,false),(36,false),(5,true)]
theorem der_79516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79516 :=
  CNF.rup_sound cl_79516 [cl_79515,cl_50697,cl_77652,cl_77651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79515 v h) (hints_cons _ _ _ (der_50697 v h) (hints_cons _ _ _ (der_77652 v h) (hints_cons _ _ _ (der_77651 v h) (by intro d hd; cases hd)))))
def cl_79517 : CNF.NClause := [(26,false),(17,false),(83,true),(5,true)]
theorem der_79517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79517 :=
  CNF.rup_sound cl_79517 [cl_77239,cl_30245,cl_51543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77239 v h) (hints_cons _ _ _ (der_30245 v h) (hints_cons _ _ _ (der_51543 v h) (by intro d hd; cases hd))))
def cl_79518 : CNF.NClause := [(82,false),(38,false),(71,true),(7,true)]
theorem der_79518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79518 :=
  CNF.rup_sound cl_79518 [cl_78146,cl_78122,cl_77442,cl_37234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78146 v h) (hints_cons _ _ _ (der_78122 v h) (hints_cons _ _ _ (der_77442 v h) (hints_cons _ _ _ (der_37234 v h) (by intro d hd; cases hd)))))
def cl_79519 : CNF.NClause := [(38,false),(71,true),(7,true)]
theorem der_79519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79519 :=
  CNF.rup_sound cl_79519 [cl_79518,cl_78139,cl_51157,cl_78140,cl_78131,cl_51150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79518 v h) (hints_cons _ _ _ (der_78139 v h) (hints_cons _ _ _ (der_51157 v h) (hints_cons _ _ _ (der_78140 v h) (hints_cons _ _ _ (der_78131 v h) (hints_cons _ _ _ (der_51150 v h) (by intro d hd; cases hd)))))))
def cl_79520 : CNF.NClause := [(89,false),(38,false),(71,false),(7,true)]
theorem der_79520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79520 :=
  CNF.rup_sound cl_79520 [cl_78134,cl_78150,cl_78151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78134 v h) (hints_cons _ _ _ (der_78150 v h) (hints_cons _ _ _ (der_78151 v h) (by intro d hd; cases hd))))
def cl_79521 : CNF.NClause := [(73,false),(38,false),(71,false),(7,true)]
theorem der_79521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79521 :=
  CNF.rup_sound cl_79521 [cl_78153,cl_79520,cl_78142,cl_51144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78153 v h) (hints_cons _ _ _ (der_79520 v h) (hints_cons _ _ _ (der_78142 v h) (hints_cons _ _ _ (der_51144 v h) (by intro d hd; cases hd)))))
def cl_79522 : CNF.NClause := [(80,false),(38,false),(71,false),(7,true)]
theorem der_79522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79522 :=
  CNF.rup_sound cl_79522 [cl_79521,cl_79520,cl_78647,cl_78150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79521 v h) (hints_cons _ _ _ (der_79520 v h) (hints_cons _ _ _ (der_78647 v h) (hints_cons _ _ _ (der_78150 v h) (by intro d hd; cases hd)))))
def cl_79523 : CNF.NClause := [(38,false),(7,true)]
theorem der_79523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79523 :=
  CNF.rup_sound cl_79523 [cl_79519,cl_79520,cl_79521,cl_79522,cl_78154,cl_78155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79519 v h) (hints_cons _ _ _ (der_79520 v h) (hints_cons _ _ _ (der_79521 v h) (hints_cons _ _ _ (der_79522 v h) (hints_cons _ _ _ (der_78154 v h) (hints_cons _ _ _ (der_78155 v h) (by intro d hd; cases hd)))))))
def cl_79524 : CNF.NClause := [(64,true),(48,false),(70,true),(17,true)]
theorem der_79524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79524 :=
  CNF.rup_sound cl_79524 [cl_78056,cl_78059,cl_78040,cl_78062,cl_51023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78056 v h) (hints_cons _ _ _ (der_78059 v h) (hints_cons _ _ _ (der_78040 v h) (hints_cons _ _ _ (der_78062 v h) (hints_cons _ _ _ (der_51023 v h) (by intro d hd; cases hd))))))
def cl_79525 : CNF.NClause := [(88,false),(76,false),(48,false),(17,true)]
theorem der_79525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79525 :=
  CNF.rup_sound cl_79525 [cl_78036,cl_52028,cl_79524,cl_33171,cl_33184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78036 v h) (hints_cons _ _ _ (der_52028 v h) (hints_cons _ _ _ (der_79524 v h) (hints_cons _ _ _ (der_33171 v h) (hints_cons _ _ _ (der_33184 v h) (by intro d hd; cases hd))))))
def cl_79526 : CNF.NClause := [(64,false),(76,false),(48,false),(17,true)]
theorem der_79526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79526 :=
  CNF.rup_sound cl_79526 [cl_79525,cl_78058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79525 v h) (hints_cons _ _ _ (der_78058 v h) (by intro d hd; cases hd)))
def cl_79527 : CNF.NClause := [(70,false),(76,true),(48,false),(17,true)]
theorem der_79527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79527 :=
  CNF.rup_sound cl_79527 [cl_78053,cl_78047,cl_51020,cl_78025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78053 v h) (hints_cons _ _ _ (der_78047 v h) (hints_cons _ _ _ (der_51020 v h) (hints_cons _ _ _ (der_78025 v h) (by intro d hd; cases hd)))))
def cl_79528 : CNF.NClause := [(76,true),(48,false),(17,true)]
theorem der_79528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79528 :=
  CNF.rup_sound cl_79528 [cl_79527,cl_79524,cl_78060,cl_78049,cl_78030,cl_78025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79527 v h) (hints_cons _ _ _ (der_79524 v h) (hints_cons _ _ _ (der_78060 v h) (hints_cons _ _ _ (der_78049 v h) (hints_cons _ _ _ (der_78030 v h) (hints_cons _ _ _ (der_78025 v h) (by intro d hd; cases hd)))))))
def cl_79529 : CNF.NClause := [(48,false),(17,true)]
theorem der_79529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79529 :=
  CNF.rup_sound cl_79529 [cl_79528,cl_79525,cl_79526,cl_79524,cl_52427,cl_78047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79528 v h) (hints_cons _ _ _ (der_79525 v h) (hints_cons _ _ _ (der_79526 v h) (hints_cons _ _ _ (der_79524 v h) (hints_cons _ _ _ (der_52427 v h) (hints_cons _ _ _ (der_78047 v h) (by intro d hd; cases hd)))))))
def cl_79530 : CNF.NClause := [(82,true),(69,true),(40,false),(9,true)]
theorem der_79530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79530 :=
  CNF.rup_sound cl_79530 [cl_77817,cl_79475,cl_50828,cl_50834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77817 v h) (hints_cons _ _ _ (der_79475 v h) (hints_cons _ _ _ (der_50828 v h) (hints_cons _ _ _ (der_50834 v h) (by intro d hd; cases hd)))))
def cl_79531 : CNF.NClause := [(69,false),(81,false),(40,false),(9,true)]
theorem der_79531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79531 :=
  CNF.rup_sound cl_79531 [cl_77693,cl_77808,cl_77777,cl_50851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77693 v h) (hints_cons _ _ _ (der_77808 v h) (hints_cons _ _ _ (der_77777 v h) (hints_cons _ _ _ (der_50851 v h) (by intro d hd; cases hd)))))
def cl_79532 : CNF.NClause := [(69,false),(40,false),(9,true)]
theorem der_79532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79532 :=
  CNF.rup_sound cl_79532 [cl_79531,cl_50859,cl_79475,cl_50832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79531 v h) (hints_cons _ _ _ (der_50859 v h) (hints_cons _ _ _ (der_79475 v h) (hints_cons _ _ _ (der_50832 v h) (by intro d hd; cases hd)))))
def cl_79533 : CNF.NClause := [(83,false),(80,false),(42,false),(11,true)]
theorem der_79533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79533 :=
  CNF.rup_sound cl_79533 [cl_50939,cl_50927,cl_77950,cl_77956,cl_77949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50939 v h) (hints_cons _ _ _ (der_50927 v h) (hints_cons _ _ _ (der_77950 v h) (hints_cons _ _ _ (der_77956 v h) (hints_cons _ _ _ (der_77949 v h) (by intro d hd; cases hd))))))
def cl_79534 : CNF.NClause := [(72,false),(83,false),(42,false),(11,true)]
theorem der_79534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79534 :=
  CNF.rup_sound cl_79534 [cl_77971,cl_79533,cl_52357,cl_77951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77971 v h) (hints_cons _ _ _ (der_79533 v h) (hints_cons _ _ _ (der_52357 v h) (hints_cons _ _ _ (der_77951 v h) (by intro d hd; cases hd)))))
def cl_79535 : CNF.NClause := [(81,false),(46,false),(79,false),(15,true)]
theorem der_79535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79535 :=
  CNF.rup_sound cl_79535 [cl_50899,cl_50914,cl_50915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50899 v h) (hints_cons _ _ _ (der_50914 v h) (hints_cons _ _ _ (der_50915 v h) (by intro d hd; cases hd))))
def cl_79536 : CNF.NClause := [(78,false),(46,false),(79,false),(15,true)]
theorem der_79536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79536 :=
  CNF.rup_sound cl_79536 [cl_79535,cl_68922,cl_77924,cl_32972,cl_50925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79535 v h) (hints_cons _ _ _ (der_68922 v h) (hints_cons _ _ _ (der_77924 v h) (hints_cons _ _ _ (der_32972 v h) (hints_cons _ _ _ (der_50925 v h) (by intro d hd; cases hd))))))
def cl_79537 : CNF.NClause := [(46,false),(79,false),(15,true)]
theorem der_79537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79537 :=
  CNF.rup_sound cl_79537 [cl_79535,cl_79536,cl_32977,cl_77920,cl_32970,cl_50923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79535 v h) (hints_cons _ _ _ (der_79536 v h) (hints_cons _ _ _ (der_32977 v h) (hints_cons _ _ _ (der_77920 v h) (hints_cons _ _ _ (der_32970 v h) (hints_cons _ _ _ (der_50923 v h) (by intro d hd; cases hd)))))))
def cl_79538 : CNF.NClause := [(78,false),(81,false),(46,false),(15,true)]
theorem der_79538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79538 :=
  CNF.rup_sound cl_79538 [cl_77934,cl_77911,cl_77936,cl_77916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77934 v h) (hints_cons _ _ _ (der_77911 v h) (hints_cons _ _ _ (der_77936 v h) (hints_cons _ _ _ (der_77916 v h) (by intro d hd; cases hd)))))
def cl_79539 : CNF.NClause := [(81,false),(46,false),(15,true)]
theorem der_79539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79539 :=
  CNF.rup_sound cl_79539 [cl_79537,cl_79538,cl_52346,cl_77917,cl_50900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79537 v h) (hints_cons _ _ _ (der_79538 v h) (hints_cons _ _ _ (der_52346 v h) (hints_cons _ _ _ (der_77917 v h) (hints_cons _ _ _ (der_50900 v h) (by intro d hd; cases hd))))))
def cl_79540 : CNF.NClause := [(80,false),(78,false),(46,false),(15,true)]
theorem der_79540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79540 :=
  CNF.rup_sound cl_79540 [cl_50921,cl_77940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50921 v h) (hints_cons _ _ _ (der_77940 v h) (by intro d hd; cases hd)))
def cl_79541 : CNF.NClause := [(91,false),(55,false),(84,false),(24,true)]
theorem der_79541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79541 :=
  CNF.rup_sound cl_79541 [cl_77871,cl_50879,cl_52305,cl_50883,cl_50875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77871 v h) (hints_cons _ _ _ (der_50879 v h) (hints_cons _ _ _ (der_52305 v h) (hints_cons _ _ _ (der_50883 v h) (hints_cons _ _ _ (der_50875 v h) (by intro d hd; cases hd))))))
def cl_79542 : CNF.NClause := [(67,true),(76,false),(55,false),(24,true)]
theorem der_79542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79542 :=
  CNF.rup_sound cl_79542 [cl_50892,cl_77890,cl_50886,cl_77908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50892 v h) (hints_cons _ _ _ (der_77890 v h) (hints_cons _ _ _ (der_50886 v h) (hints_cons _ _ _ (der_77908 v h) (by intro d hd; cases hd)))))
def cl_79543 : CNF.NClause := [(91,false),(76,true),(55,false),(24,true)]
theorem der_79543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79543 :=
  CNF.rup_sound cl_79543 [cl_79541,cl_50878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79541 v h) (hints_cons _ _ _ (der_50878 v h) (by intro d hd; cases hd)))
def cl_79544 : CNF.NClause := [(80,false),(76,true),(55,false),(24,true)]
theorem der_79544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79544 :=
  CNF.rup_sound cl_79544 [cl_77084,cl_77903,cl_77905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77084 v h) (hints_cons _ _ _ (der_77903 v h) (hints_cons _ _ _ (der_77905 v h) (by intro d hd; cases hd))))
def cl_79545 : CNF.NClause := [(63,false),(55,false),(24,true)]
theorem der_79545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79545 :=
  CNF.rup_sound cl_79545 [cl_77084,cl_79542,cl_50893,cl_79541,cl_77876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77084 v h) (hints_cons _ _ _ (der_79542 v h) (hints_cons _ _ _ (der_50893 v h) (hints_cons _ _ _ (der_79541 v h) (hints_cons _ _ _ (der_77876 v h) (by intro d hd; cases hd))))))
def cl_79546 : CNF.NClause := [(74,true),(50,false),(19,true)]
theorem der_79546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79546 :=
  CNF.rup_sound cl_79546 [cl_79467,cl_78351,cl_51453,cl_77196,cl_78348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79467 v h) (hints_cons _ _ _ (der_78351 v h) (hints_cons _ _ _ (der_51453 v h) (hints_cons _ _ _ (der_77196 v h) (hints_cons _ _ _ (der_78348 v h) (by intro d hd; cases hd))))))
def cl_79547 : CNF.NClause := [(50,false),(19,true)]
theorem der_79547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79547 :=
  CNF.rup_sound cl_79547 [cl_79546,cl_79469,cl_51455,cl_51447,cl_51446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79546 v h) (hints_cons _ _ _ (der_79469 v h) (hints_cons _ _ _ (der_51455 v h) (hints_cons _ _ _ (der_51447 v h) (hints_cons _ _ _ (der_51446 v h) (by intro d hd; cases hd))))))
def cl_79548 : CNF.NClause := [(88,false),(52,false),(79,false),(21,true)]
theorem der_79548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79548 :=
  CNF.rup_sound cl_79548 [cl_51652,cl_51766,cl_78431,cl_46980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51652 v h) (hints_cons _ _ _ (der_51766 v h) (hints_cons _ _ _ (der_78431 v h) (hints_cons _ _ _ (der_46980 v h) (by intro d hd; cases hd)))))
def cl_79549 : CNF.NClause := [(67,false),(52,false),(79,false),(21,true)]
theorem der_79549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79549 :=
  CNF.rup_sound cl_79549 [cl_78431,cl_79548,cl_34586,cl_51579,cl_34309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78431 v h) (hints_cons _ _ _ (der_79548 v h) (hints_cons _ _ _ (der_34586 v h) (hints_cons _ _ _ (der_51579 v h) (hints_cons _ _ _ (der_34309 v h) (by intro d hd; cases hd))))))
def cl_79550 : CNF.NClause := [(52,false),(79,false),(21,true)]
theorem der_79550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79550 :=
  CNF.rup_sound cl_79550 [cl_79549,cl_50593,cl_79548,cl_78432,cl_51856,cl_34444] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79549 v h) (hints_cons _ _ _ (der_50593 v h) (hints_cons _ _ _ (der_79548 v h) (hints_cons _ _ _ (der_78432 v h) (hints_cons _ _ _ (der_51856 v h) (hints_cons _ _ _ (der_34444 v h) (by intro d hd; cases hd)))))))
def cl_79551 : CNF.NClause := [(88,false),(85,false),(52,false),(21,true)]
theorem der_79551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79551 :=
  CNF.rup_sound cl_79551 [cl_79550,cl_52081,cl_51650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79550 v h) (hints_cons _ _ _ (der_52081 v h) (hints_cons _ _ _ (der_51650 v h) (by intro d hd; cases hd))))
def cl_79552 : CNF.NClause := [(67,false),(85,false),(52,false),(21,true)]
theorem der_79552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79552 :=
  CNF.rup_sound cl_79552 [cl_79550,cl_79551,cl_51769,cl_51868,cl_78429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79550 v h) (hints_cons _ _ _ (der_79551 v h) (hints_cons _ _ _ (der_51769 v h) (hints_cons _ _ _ (der_51868 v h) (hints_cons _ _ _ (der_78429 v h) (by intro d hd; cases hd))))))
def cl_79553 : CNF.NClause := [(85,false),(52,false),(21,true)]
theorem der_79553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79553 :=
  CNF.rup_sound cl_79553 [cl_79552,cl_79551,cl_79550,cl_78430,cl_51857,cl_50592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79552 v h) (hints_cons _ _ _ (der_79551 v h) (hints_cons _ _ _ (der_79550 v h) (hints_cons _ _ _ (der_78430 v h) (hints_cons _ _ _ (der_51857 v h) (hints_cons _ _ _ (der_50592 v h) (by intro d hd; cases hd)))))))
def cl_79554 : CNF.NClause := [(52,false),(21,true)]
theorem der_79554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79554 :=
  CNF.rup_sound cl_79554 [cl_79550,cl_79553,cl_78435,cl_78433,cl_51767,cl_77300,cl_78461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79550 v h) (hints_cons _ _ _ (der_79553 v h) (hints_cons _ _ _ (der_78435 v h) (hints_cons _ _ _ (der_78433 v h) (hints_cons _ _ _ (der_51767 v h) (hints_cons _ _ _ (der_77300 v h) (hints_cons _ _ _ (der_78461 v h) (by intro d hd; cases hd))))))))
def cl_79555 : CNF.NClause := [(91,false),(81,false),(43,false),(12,true)]
theorem der_79555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79555 :=
  CNF.rup_sound cl_79555 [cl_79461,cl_78065,cl_51042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79461 v h) (hints_cons _ _ _ (der_78065 v h) (hints_cons _ _ _ (der_51042 v h) (by intro d hd; cases hd))))
def cl_79556 : CNF.NClause := [(85,true),(81,false),(43,false),(12,true)]
theorem der_79556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79556 :=
  CNF.rup_sound cl_79556 [cl_79461,cl_79555,cl_78092,cl_78091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79461 v h) (hints_cons _ _ _ (der_79555 v h) (hints_cons _ _ _ (der_78092 v h) (hints_cons _ _ _ (der_78091 v h) (by intro d hd; cases hd)))))
def cl_79557 : CNF.NClause := [(85,false),(43,false),(12,true)]
theorem der_79557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79557 :=
  CNF.rup_sound cl_79557 [cl_79484,cl_79461,cl_51064,cl_51057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79484 v h) (hints_cons _ _ _ (der_79461 v h) (hints_cons _ _ _ (der_51064 v h) (hints_cons _ _ _ (der_51057 v h) (by intro d hd; cases hd)))))
def cl_79558 : CNF.NClause := [(81,false),(59,false),(84,false),(28,true)]
theorem der_79558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79558 :=
  CNF.rup_sound cl_79558 [cl_51176,cl_79482,cl_51178,cl_78178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51176 v h) (hints_cons _ _ _ (der_79482 v h) (hints_cons _ _ _ (der_51178 v h) (hints_cons _ _ _ (der_78178 v h) (by intro d hd; cases hd)))))
def cl_79559 : CNF.NClause := [(59,false),(84,false),(28,true)]
theorem der_79559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79559 :=
  CNF.rup_sound cl_79559 [cl_79558,cl_78177,cl_78178,cl_51183,cl_78163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79558 v h) (hints_cons _ _ _ (der_78177 v h) (hints_cons _ _ _ (der_78178 v h) (hints_cons _ _ _ (der_51183 v h) (hints_cons _ _ _ (der_78163 v h) (by intro d hd; cases hd))))))
def cl_79560 : CNF.NClause := [(62,true),(73,true),(59,false),(28,true)]
theorem der_79560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79560 :=
  CNF.rup_sound cl_79560 [cl_79559,cl_51171,cl_79482,cl_51202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79559 v h) (hints_cons _ _ _ (der_51171 v h) (hints_cons _ _ _ (der_79482 v h) (hints_cons _ _ _ (der_51202 v h) (by intro d hd; cases hd)))))
def cl_79561 : CNF.NClause := [(81,true),(59,false),(28,true)]
theorem der_79561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79561 :=
  CNF.rup_sound cl_79561 [cl_79559,cl_78186,cl_79560,cl_51199,cl_51171,cl_79482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79559 v h) (hints_cons _ _ _ (der_78186 v h) (hints_cons _ _ _ (der_79560 v h) (hints_cons _ _ _ (der_51199 v h) (hints_cons _ _ _ (der_51171 v h) (hints_cons _ _ _ (der_79482 v h) (by intro d hd; cases hd)))))))
def cl_79562 : CNF.NClause := [(82,false),(37,false),(70,true),(6,true)]
theorem der_79562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79562 :=
  CNF.rup_sound cl_79562 [cl_50548,cl_77636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50548 v h) (hints_cons _ _ _ (der_77636 v h) (by intro d hd; cases hd)))
def cl_79563 : CNF.NClause := [(74,false),(37,false),(70,true),(6,true)]
theorem der_79563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79563 :=
  CNF.rup_sound cl_79563 [cl_79562,cl_49711,cl_77643,cl_77641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79562 v h) (hints_cons _ _ _ (der_49711 v h) (hints_cons _ _ _ (der_77643 v h) (hints_cons _ _ _ (der_77641 v h) (by intro d hd; cases hd)))))
def cl_79564 : CNF.NClause := [(67,false),(71,true),(51,false),(20,true)]
theorem der_79564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79564 :=
  CNF.rup_sound cl_79564 [cl_51413,cl_51388,cl_78290,cl_78311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51413 v h) (hints_cons _ _ _ (der_51388 v h) (hints_cons _ _ _ (der_78290 v h) (hints_cons _ _ _ (der_78311 v h) (by intro d hd; cases hd)))))
def cl_79565 : CNF.NClause := [(70,false),(71,true),(51,false),(20,true)]
theorem der_79565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79565 :=
  CNF.rup_sound cl_79565 [cl_79564,cl_78315,cl_51400,cl_78295,cl_78317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79564 v h) (hints_cons _ _ _ (der_78315 v h) (hints_cons _ _ _ (der_51400 v h) (hints_cons _ _ _ (der_78295 v h) (hints_cons _ _ _ (der_78317 v h) (by intro d hd; cases hd))))))
def cl_79566 : CNF.NClause := [(68,false),(71,false),(51,false),(20,true)]
theorem der_79566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79566 :=
  CNF.rup_sound cl_79566 [cl_78303,cl_51394,cl_78307,cl_78301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78303 v h) (hints_cons _ _ _ (der_51394 v h) (hints_cons _ _ _ (der_78307 v h) (hints_cons _ _ _ (der_78301 v h) (by intro d hd; cases hd)))))
def cl_79567 : CNF.NClause := [(69,false),(68,true),(51,false),(20,true)]
theorem der_79567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79567 :=
  CNF.rup_sound cl_79567 [cl_51409,cl_51382,cl_51408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51409 v h) (hints_cons _ _ _ (der_51382 v h) (hints_cons _ _ _ (der_51408 v h) (by intro d hd; cases hd))))
def cl_79568 : CNF.NClause := [(32,false),(76,false),(71,true),(1,true)]
theorem der_79568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79568 :=
  CNF.rup_sound cl_79568 [cl_51496,cl_51477,cl_34144,cl_34157,cl_51486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51496 v h) (hints_cons _ _ _ (der_51477 v h) (hints_cons _ _ _ (der_34144 v h) (hints_cons _ _ _ (der_34157 v h) (hints_cons _ _ _ (der_51486 v h) (by intro d hd; cases hd))))))
def cl_79569 : CNF.NClause := [(32,false),(86,false),(71,false),(1,true)]
theorem der_79569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79569 :=
  CNF.rup_sound cl_79569 [cl_51485,cl_51483,cl_78380,cl_52637,cl_78358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51485 v h) (hints_cons _ _ _ (der_51483 v h) (hints_cons _ _ _ (der_78380 v h) (hints_cons _ _ _ (der_52637 v h) (hints_cons _ _ _ (der_78358 v h) (by intro d hd; cases hd))))))
def cl_79570 : CNF.NClause := [(65,true),(34,false),(70,true),(3,true)]
theorem der_79570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79570 :=
  CNF.rup_sound cl_79570 [cl_78019,cl_50978,cl_50989,cl_50992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78019 v h) (hints_cons _ _ _ (der_50978 v h) (hints_cons _ _ _ (der_50989 v h) (hints_cons _ _ _ (der_50992 v h) (by intro d hd; cases hd)))))
def cl_79571 : CNF.NClause := [(70,false),(75,false),(34,false),(3,true)]
theorem der_79571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79571 :=
  CNF.rup_sound cl_79571 [cl_61268,cl_77998,cl_50986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61268 v h) (hints_cons _ _ _ (der_77998 v h) (hints_cons _ _ _ (der_50986 v h) (by intro d hd; cases hd))))
def cl_79572 : CNF.NClause := [(65,true),(34,false),(3,true)]
theorem der_79572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79572 :=
  CNF.rup_sound cl_79572 [cl_79570,cl_79571,cl_78022,cl_78003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79570 v h) (hints_cons _ _ _ (der_79571 v h) (hints_cons _ _ _ (der_78022 v h) (hints_cons _ _ _ (der_78003 v h) (by intro d hd; cases hd)))))
def cl_79573 : CNF.NClause := [(75,true),(85,false),(34,false),(3,true)]
theorem der_79573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79573 :=
  CNF.rup_sound cl_79573 [cl_78012,cl_79572,cl_53652,cl_52400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78012 v h) (hints_cons _ _ _ (der_79572 v h) (hints_cons _ _ _ (der_53652 v h) (hints_cons _ _ _ (der_52400 v h) (by intro d hd; cases hd)))))
def cl_79574 : CNF.NClause := [(85,true),(80,false),(34,false),(3,true)]
theorem der_79574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79574 :=
  CNF.rup_sound cl_79574 [cl_79572,cl_78018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79572 v h) (hints_cons _ _ _ (der_78018 v h) (by intro d hd; cases hd)))
def cl_79575 : CNF.NClause := [(68,false),(78,false),(35,false),(4,true)]
theorem der_79575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79575 :=
  CNF.rup_sound cl_79575 [cl_77161,cl_59959,cl_78234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77161 v h) (hints_cons _ _ _ (der_59959 v h) (hints_cons _ _ _ (der_78234 v h) (by intro d hd; cases hd))))
def cl_79576 : CNF.NClause := [(73,true),(78,false),(35,false),(4,true)]
theorem der_79576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79576 :=
  CNF.rup_sound cl_79576 [cl_78241,cl_79575,cl_78257,cl_52560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78241 v h) (hints_cons _ _ _ (der_79575 v h) (hints_cons _ _ _ (der_78257 v h) (hints_cons _ _ _ (der_52560 v h) (by intro d hd; cases hd)))))
def cl_79577 : CNF.NClause := [(78,false),(35,false),(4,true)]
theorem der_79577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79577 :=
  CNF.rup_sound cl_79577 [cl_79575,cl_79576,cl_78236,cl_78238,cl_78250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79575 v h) (hints_cons _ _ _ (der_79576 v h) (hints_cons _ _ _ (der_78236 v h) (hints_cons _ _ _ (der_78238 v h) (hints_cons _ _ _ (der_78250 v h) (by intro d hd; cases hd))))))
def cl_79578 : CNF.NClause := [(68,false),(35,false),(4,true)]
theorem der_79578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79578 :=
  CNF.rup_sound cl_79578 [cl_79577,cl_79480,cl_51297,cl_78256,cl_51311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79577 v h) (hints_cons _ _ _ (der_79480 v h) (hints_cons _ _ _ (der_51297 v h) (hints_cons _ _ _ (der_78256 v h) (hints_cons _ _ _ (der_51311 v h) (by intro d hd; cases hd))))))
def cl_79579 : CNF.NClause := [(76,true),(41,false),(74,true),(10,true)]
theorem der_79579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79579 :=
  CNF.rup_sound cl_79579 [cl_79462,cl_51267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79462 v h) (hints_cons _ _ _ (der_51267 v h) (by intro d hd; cases hd)))
def cl_79581 : CNF.NClause := [(72,false),(73,false),(41,false),(10,true)]
theorem der_79581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79581 :=
  CNF.rup_sound cl_79581 [cl_79462,cl_78198,cl_78211,cl_78219,cl_51257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79462 v h) (hints_cons _ _ _ (der_78198 v h) (hints_cons _ _ _ (der_78211 v h) (hints_cons _ _ _ (der_78219 v h) (hints_cons _ _ _ (der_51257 v h) (by intro d hd; cases hd))))))
def cl_79582 : CNF.NClause := [(67,true),(65,true),(54,false),(23,true)]
theorem der_79582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79582 :=
  CNF.rup_sound cl_79582 [cl_50809,cl_50777,cl_77756,cl_77744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50809 v h) (hints_cons _ _ _ (der_50777 v h) (hints_cons _ _ _ (der_77756 v h) (hints_cons _ _ _ (der_77744 v h) (by intro d hd; cases hd)))))
def cl_79583 : CNF.NClause := [(65,false),(74,false),(54,false),(23,true)]
theorem der_79583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79583 :=
  CNF.rup_sound cl_79583 [cl_50802,cl_50776,cl_77773,cl_77764,cl_52202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50802 v h) (hints_cons _ _ _ (der_50776 v h) (hints_cons _ _ _ (der_77773 v h) (hints_cons _ _ _ (der_77764 v h) (hints_cons _ _ _ (der_52202 v h) (by intro d hd; cases hd))))))
def cl_79584 : CNF.NClause := [(83,true),(67,false),(54,false),(23,true)]
theorem der_79584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79584 :=
  CNF.rup_sound cl_79584 [cl_50807,cl_77749,cl_77754,cl_79583,cl_50778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50807 v h) (hints_cons _ _ _ (der_77749 v h) (hints_cons _ _ _ (der_77754 v h) (hints_cons _ _ _ (der_79583 v h) (hints_cons _ _ _ (der_50778 v h) (by intro d hd; cases hd))))))
def cl_79585 : CNF.NClause := [(60,false),(88,false),(74,true),(29,true)]
theorem der_79585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79585 :=
  CNF.rup_sound cl_79585 [cl_77834,cl_32728,cl_77859,cl_50864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77834 v h) (hints_cons _ _ _ (der_32728 v h) (hints_cons _ _ _ (der_77859 v h) (hints_cons _ _ _ (der_50864 v h) (by intro d hd; cases hd)))))
def cl_79586 : CNF.NClause := [(68,false),(60,false),(88,false),(29,true)]
theorem der_79586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79586 :=
  CNF.rup_sound cl_79586 [cl_79585,cl_50862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79585 v h) (hints_cons _ _ _ (der_50862 v h) (by intro d hd; cases hd)))
def cl_79588 : CNF.NClause := [(26,false),(83,true),(75,false),(57,false)]
theorem der_79588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79588 :=
  CNF.rup_sound cl_79588 [cl_78277,cl_79463,cl_61646,cl_15867,cl_42754,cl_15886,cl_76643,cl_15885,cl_76591,cl_15879,cl_76593,cl_15873,cl_29835,cl_15894,cl_29837,cl_15892,cl_29836,cl_15893,cl_15667,cl_12672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78277 v h) (hints_cons _ _ _ (der_79463 v h) (hints_cons _ _ _ (der_61646 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_42754 v h) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_76643 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_76591 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_76593 v h) (hints_cons _ _ _ (der_15873 v h) (hints_cons _ _ _ (der_29835 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_29837 v h) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_29836 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (inp_12672 v h) (by intro d hd; cases hd)))))))))))))))))))))
def cl_79589 : CNF.NClause := [(79,true),(71,false),(57,false)]
theorem der_79589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79589 :=
  CNF.rup_sound cl_79589 [cl_79508,cl_79463,cl_78279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79508 v h) (hints_cons _ _ _ (der_79463 v h) (hints_cons _ _ _ (der_78279 v h) (by intro d hd; cases hd))))
def cl_79591 : CNF.NClause := [(77,false),(91,false),(69,true),(49,false)]
theorem der_79591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79591 :=
  CNF.rup_sound cl_79591 [cl_78485,cl_77473,cl_77479,cl_79466,cl_49719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78485 v h) (hints_cons _ _ _ (der_77473 v h) (hints_cons _ _ _ (der_77479 v h) (hints_cons _ _ _ (der_79466 v h) (hints_cons _ _ _ (der_49719 v h) (by intro d hd; cases hd))))))
def cl_79592 : CNF.NClause := [(91,false),(73,true),(86,false),(49,false)]
theorem der_79592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79592 :=
  CNF.rup_sound cl_79592 [cl_79466,cl_50551,cl_78454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79466 v h) (hints_cons _ _ _ (der_50551 v h) (hints_cons _ _ _ (der_78454 v h) (by intro d hd; cases hd))))
def cl_79593 : CNF.NClause := [(77,true),(69,false),(73,false),(49,false)]
theorem der_79593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79593 :=
  CNF.rup_sound cl_79593 [cl_77682,cl_77479,cl_79466,cl_78455,cl_51843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77682 v h) (hints_cons _ _ _ (der_77479 v h) (hints_cons _ _ _ (der_79466 v h) (hints_cons _ _ _ (der_78455 v h) (hints_cons _ _ _ (der_51843 v h) (by intro d hd; cases hd))))))
def cl_79594 : CNF.NClause := [(65,false),(86,true),(73,false),(49,false)]
theorem der_79594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79594 :=
  CNF.rup_sound cl_79594 [cl_51850,cl_77473,cl_78455,cl_79591,cl_41231,cl_15922,cl_50005,cl_15934,cl_76581,cl_15907,cl_49789,cl_15911,cl_76622,cl_15920,cl_42488,cl_15928,cl_13694,cl_36157,cl_15921,cl_76641,cl_15925,cl_76608,cl_15923,cl_15740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51850 v h) (hints_cons _ _ _ (der_77473 v h) (hints_cons _ _ _ (der_78455 v h) (hints_cons _ _ _ (der_79591 v h) (hints_cons _ _ _ (der_41231 v h) (hints_cons _ _ _ (der_15922 v h) (hints_cons _ _ _ (der_50005 v h) (hints_cons _ _ _ (der_15934 v h) (hints_cons _ _ _ (der_76581 v h) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_49789 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_76622 v h) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_42488 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (inp_13694 v h) (hints_cons _ _ _ (der_36157 v h) (hints_cons _ _ _ (der_15921 v h) (hints_cons _ _ _ (der_76641 v h) (hints_cons _ _ _ (der_15925 v h) (hints_cons _ _ _ (der_76608 v h) (hints_cons _ _ _ (der_15923 v h) (hints_cons _ _ _ (der_15740 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_79595 : CNF.NClause := [(132,false),(76,true)]
theorem der_79595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79595 :=
  CNF.rup_sound cl_79595 [cl_65746,cl_61991,cl_76527,cl_76525,cl_63761,cl_8056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65746 v h) (hints_cons _ _ _ (der_61991 v h) (hints_cons _ _ _ (der_76527 v h) (hints_cons _ _ _ (der_76525 v h) (hints_cons _ _ _ (der_63761 v h) (hints_cons _ _ _ (inp_8056 v h) (by intro d hd; cases hd)))))))
def cl_79596 : CNF.NClause := [(58,true),(151,false),(23,false)]
theorem der_79596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79596 :=
  CNF.rup_sound cl_79596 [cl_76527,cl_65751,cl_61644,cl_15792,cl_76546,cl_78650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76527 v h) (hints_cons _ _ _ (der_65751 v h) (hints_cons _ _ _ (der_61644 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_76546 v h) (hints_cons _ _ _ (der_78650 v h) (by intro d hd; cases hd)))))))
def cl_79597 : CNF.NClause := [(1055,false),(76,true)]
theorem der_79597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79597 :=
  CNF.rup_sound cl_79597 [cl_15907,cl_63467,cl_15932,cl_76876,cl_77228,cl_15930,cl_76627,cl_15923,cl_15914,cl_49531,cl_15916,cl_13637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_63467 v h) (hints_cons _ _ _ (der_15932 v h) (hints_cons _ _ _ (der_76876 v h) (hints_cons _ _ _ (der_77228 v h) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_76627 v h) (hints_cons _ _ _ (der_15923 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_49531 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (inp_13637 v h) (by intro d hd; cases hd)))))))))))))
def cl_79599 : CNF.NClause := [(102,true),(32,false),(38,false)]
theorem der_79599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79599 :=
  CNF.rup_sound cl_79599 [cl_50092,cl_76770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50092 v h) (hints_cons _ _ _ (der_76770 v h) (by intro d hd; cases hd)))
def cl_79600 : CNF.NClause := [(102,true),(57,false),(38,false)]
theorem der_79600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79600 :=
  CNF.rup_sound cl_79600 [cl_77416,cl_76770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77416 v h) (hints_cons _ _ _ (der_76770 v h) (by intro d hd; cases hd)))
def cl_79602 : CNF.NClause := [(95,true),(43,false),(33,false)]
theorem der_79602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79602 :=
  CNF.rup_sound cl_79602 [cl_54869,cl_76707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54869 v h) (hints_cons _ _ _ (der_76707 v h) (by intro d hd; cases hd)))
def cl_79609 : CNF.NClause := [(41,false),(32,false),(107,true)]
theorem der_79609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79609 :=
  CNF.rup_sound cl_79609 [cl_77340,cl_76887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77340 v h) (hints_cons _ _ _ (der_76887 v h) (by intro d hd; cases hd)))
def cl_79616 : CNF.NClause := [(77,true),(914,false)]
theorem der_79616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79616 :=
  CNF.rup_sound cl_79616 [cl_76805,cl_15881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76805 v h) (hints_cons _ _ _ (der_15881 v h) (by intro d hd; cases hd)))
def cl_79617 : CNF.NClause := [(91,true),(1060,false)]
theorem der_79617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79617 :=
  CNF.rup_sound cl_79617 [cl_76812,cl_15912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76812 v h) (hints_cons _ _ _ (der_15912 v h) (by intro d hd; cases hd)))
def cl_79618 : CNF.NClause := [(88,true),(908,false)]
theorem der_79618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79618 :=
  CNF.rup_sound cl_79618 [cl_76837,cl_76539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76837 v h) (hints_cons _ _ _ (der_76539 v h) (by intro d hd; cases hd)))
def cl_79619 : CNF.NClause := [(64,true),(141,false)]
theorem der_79619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79619 :=
  CNF.rup_sound cl_79619 [cl_76849,cl_15783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76849 v h) (hints_cons _ _ _ (der_15783 v h) (by intro d hd; cases hd)))
def cl_79620 : CNF.NClause := [(70,true),(152,false)]
theorem der_79620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79620 :=
  CNF.rup_sound cl_79620 [cl_76871,cl_15793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76871 v h) (hints_cons _ _ _ (der_15793 v h) (by intro d hd; cases hd)))
def cl_79621 : CNF.NClause := [(75,true),(133,false)]
theorem der_79621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79621 :=
  CNF.rup_sound cl_79621 [cl_76875,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76875 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_79622 : CNF.NClause := [(75,true),(127,false)]
theorem der_79622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79622 :=
  CNF.rup_sound cl_79622 [cl_76888,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76888 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_79623 : CNF.NClause := [(72,true),(135,false)]
theorem der_79623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79623 :=
  CNF.rup_sound cl_79623 [cl_76912,cl_62596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76912 v h) (hints_cons _ _ _ (der_62596 v h) (by intro d hd; cases hd)))
def cl_79624 : CNF.NClause := [(76,true),(151,false)]
theorem der_79624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79624 :=
  CNF.rup_sound cl_79624 [cl_76926,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76926 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_79625 : CNF.NClause := [(63,true),(143,false)]
theorem der_79625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79625 :=
  CNF.rup_sound cl_79625 [cl_76952,cl_76534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76952 v h) (hints_cons _ _ _ (der_76534 v h) (by intro d hd; cases hd)))
def cl_79626 : CNF.NClause := [(70,true),(144,false)]
theorem der_79626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79626 :=
  CNF.rup_sound cl_79626 [cl_77000,cl_62587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77000 v h) (hints_cons _ _ _ (der_62587 v h) (by intro d hd; cases hd)))
def cl_79627 : CNF.NClause := [(68,true),(136,false)]
theorem der_79627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79627 :=
  CNF.rup_sound cl_79627 [cl_77008,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77008 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_79628 : CNF.NClause := [(133,false),(81,true)]
theorem der_79628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79628 :=
  CNF.rup_sound cl_79628 [cl_77009,cl_15775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77009 v h) (hints_cons _ _ _ (der_15775 v h) (by intro d hd; cases hd)))
def cl_79629 : CNF.NClause := [(79,true),(39,false)]
theorem der_79629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79629 :=
  CNF.rup_sound cl_79629 [cl_79481,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79481 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79630 : CNF.NClause := [(52,false),(79,true)]
theorem der_79630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79630 :=
  CNF.rup_sound cl_79630 [cl_79489,cl_79554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79489 v h) (hints_cons _ _ _ (der_79554 v h) (by intro d hd; cases hd)))
def cl_79631 : CNF.NClause := [(6,false),(10,false),(74,true)]
theorem der_79631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79631 :=
  CNF.rup_sound cl_79631 [cl_77021,cl_76890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77021 v h) (hints_cons _ _ _ (der_76890 v h) (by intro d hd; cases hd)))
def cl_79632 : CNF.NClause := [(4,false),(8,false),(68,true)]
theorem der_79632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79632 :=
  CNF.rup_sound cl_79632 [cl_50071,cl_76637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50071 v h) (hints_cons _ _ _ (der_76637 v h) (by intro d hd; cases hd)))
def cl_79633 : CNF.NClause := [(9,false),(20,false),(69,true)]
theorem der_79633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79633 :=
  CNF.rup_sound cl_79633 [cl_77028,cl_76915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77028 v h) (hints_cons _ _ _ (der_76915 v h) (by intro d hd; cases hd)))
def cl_79634 : CNF.NClause := [(11,false),(20,false),(69,true)]
theorem der_79634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79634 :=
  CNF.rup_sound cl_79634 [cl_77029,cl_47172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77029 v h) (hints_cons _ _ _ (der_47172 v h) (by intro d hd; cases hd)))
def cl_79635 : CNF.NClause := [(29,false),(20,false),(68,true)]
theorem der_79635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79635 :=
  CNF.rup_sound cl_79635 [cl_77226,cl_54215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77226 v h) (hints_cons _ _ _ (der_54215 v h) (by intro d hd; cases hd)))
def cl_79636 : CNF.NClause := [(1,false),(24,false),(76,true)]
theorem der_79636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79636 :=
  CNF.rup_sound cl_79636 [cl_77228,cl_76626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77228 v h) (hints_cons _ _ _ (der_76626 v h) (by intro d hd; cases hd)))
def cl_79637 : CNF.NClause := [(22,false),(78,true),(27,false)]
theorem der_79637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79637 :=
  CNF.rup_sound cl_79637 [cl_50107,cl_76647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50107 v h) (hints_cons _ _ _ (der_76647 v h) (by intro d hd; cases hd)))
def cl_79638 : CNF.NClause := [(3,false),(85,true),(27,false)]
theorem der_79638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79638 :=
  CNF.rup_sound cl_79638 [cl_77236,cl_76964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77236 v h) (hints_cons _ _ _ (der_76964 v h) (by intro d hd; cases hd)))
def cl_79639 : CNF.NClause := [(12,false),(85,true),(21,false)]
theorem der_79639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79639 :=
  CNF.rup_sound cl_79639 [cl_77237,cl_76619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77237 v h) (hints_cons _ _ _ (der_76619 v h) (by intro d hd; cases hd)))
def cl_79640 : CNF.NClause := [(3,false),(12,false),(85,true)]
theorem der_79640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79640 :=
  CNF.rup_sound cl_79640 [cl_54252,cl_76964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54252 v h) (hints_cons _ _ _ (der_76964 v h) (by intro d hd; cases hd)))
def cl_79641 : CNF.NClause := [(11,false),(23,false),(83,true)]
theorem der_79641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79641 :=
  CNF.rup_sound cl_79641 [cl_77240,cl_54211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77240 v h) (hints_cons _ _ _ (der_54211 v h) (by intro d hd; cases hd)))
def cl_79642 : CNF.NClause := [(16,false),(4,false),(68,true)]
theorem der_79642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79642 :=
  CNF.rup_sound cl_79642 [cl_77243,cl_49530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77243 v h) (hints_cons _ _ _ (der_49530 v h) (by intro d hd; cases hd)))
def cl_79643 : CNF.NClause := [(17,false),(76,true),(8,false)]
theorem der_79643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79643 :=
  CNF.rup_sound cl_79643 [cl_50121,cl_76627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50121 v h) (hints_cons _ _ _ (der_76627 v h) (by intro d hd; cases hd)))
def cl_79644 : CNF.NClause := [(12,false),(81,true),(23,false)]
theorem der_79644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79644 :=
  CNF.rup_sound cl_79644 [cl_77248,cl_50006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77248 v h) (hints_cons _ _ _ (der_50006 v h) (by intro d hd; cases hd)))
def cl_79645 : CNF.NClause := [(9,false),(15,false),(81,true)]
theorem der_79645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79645 :=
  CNF.rup_sound cl_79645 [cl_77250,cl_76604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77250 v h) (hints_cons _ _ _ (der_76604 v h) (by intro d hd; cases hd)))
def cl_79646 : CNF.NClause := [(11,false),(15,false),(80,true)]
theorem der_79646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79646 :=
  CNF.rup_sound cl_79646 [cl_35176,cl_76615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35176 v h) (hints_cons _ _ _ (der_76615 v h) (by intro d hd; cases hd)))
def cl_79647 : CNF.NClause := [(4,false),(13,false),(78,true)]
theorem der_79647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79647 :=
  CNF.rup_sound cl_79647 [cl_36896,cl_76930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36896 v h) (hints_cons _ _ _ (der_76930 v h) (by intro d hd; cases hd)))
def cl_79648 : CNF.NClause := [(9,false),(81,true),(23,false)]
theorem der_79648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79648 :=
  CNF.rup_sound cl_79648 [cl_50139,cl_76606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50139 v h) (hints_cons _ _ _ (der_76606 v h) (by intro d hd; cases hd)))
def cl_79649 : CNF.NClause := [(11,false),(80,true),(24,false)]
theorem der_79649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79649 :=
  CNF.rup_sound cl_79649 [cl_77251,cl_76615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77251 v h) (hints_cons _ _ _ (der_76615 v h) (by intro d hd; cases hd)))
def cl_79650 : CNF.NClause := [(78,true),(13,false),(27,false)]
theorem der_79650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79650 :=
  CNF.rup_sound cl_79650 [cl_50144,cl_76646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50144 v h) (hints_cons _ _ _ (der_76646 v h) (by intro d hd; cases hd)))
def cl_79651 : CNF.NClause := [(29,false),(3,false),(80,true)]
theorem der_79651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79651 :=
  CNF.rup_sound cl_79651 [cl_77255,cl_76874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77255 v h) (hints_cons _ _ _ (der_76874 v h) (by intro d hd; cases hd)))
def cl_79652 : CNF.NClause := [(3,false),(24,false),(80,true)]
theorem der_79652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79652 :=
  CNF.rup_sound cl_79652 [cl_77256,cl_79649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77256 v h) (hints_cons _ _ _ (der_79649 v h) (by intro d hd; cases hd)))
def cl_79653 : CNF.NClause := [(3,false),(7,false),(80,true)]
theorem der_79653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79653 :=
  CNF.rup_sound cl_79653 [cl_77257,cl_76982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77257 v h) (hints_cons _ _ _ (der_76982 v h) (by intro d hd; cases hd)))
def cl_79654 : CNF.NClause := [(9,false),(18,false),(69,true)]
theorem der_79654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79654 :=
  CNF.rup_sound cl_79654 [cl_77258,cl_79633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77258 v h) (hints_cons _ _ _ (der_79633 v h) (by intro d hd; cases hd)))
def cl_79655 : CNF.NClause := [(29,false),(24,false),(80,true)]
theorem der_79655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79655 :=
  CNF.rup_sound cl_79655 [cl_77259,cl_76959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77259 v h) (hints_cons _ _ _ (der_76959 v h) (by intro d hd; cases hd)))
def cl_79656 : CNF.NClause := [(15,false),(24,false),(80,true)]
theorem der_79656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79656 :=
  CNF.rup_sound cl_79656 [cl_77260,cl_76874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77260 v h) (hints_cons _ _ _ (der_76874 v h) (by intro d hd; cases hd)))
def cl_79657 : CNF.NClause := [(29,false),(15,false),(80,true)]
theorem der_79657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79657 :=
  CNF.rup_sound cl_79657 [cl_77261,cl_79656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77261 v h) (hints_cons _ _ _ (der_79656 v h) (by intro d hd; cases hd)))
def cl_79658 : CNF.NClause := [(24,false),(7,false),(80,true)]
theorem der_79658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79658 :=
  CNF.rup_sound cl_79658 [cl_77262,cl_76982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77262 v h) (hints_cons _ _ _ (der_76982 v h) (by intro d hd; cases hd)))
def cl_79659 : CNF.NClause := [(19,false),(21,false),(85,true)]
theorem der_79659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79659 :=
  CNF.rup_sound cl_79659 [cl_50157,cl_76935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50157 v h) (hints_cons _ _ _ (der_76935 v h) (by intro d hd; cases hd)))
def cl_79660 : CNF.NClause := [(1,false),(8,false),(76,true)]
theorem der_79660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79660 :=
  CNF.rup_sound cl_79660 [cl_77263,cl_79636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77263 v h) (hints_cons _ _ _ (der_79636 v h) (by intro d hd; cases hd)))
def cl_79661 : CNF.NClause := [(29,false),(19,false),(74,true)]
theorem der_79661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79661 :=
  CNF.rup_sound cl_79661 [cl_77264,cl_76572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77264 v h) (hints_cons _ _ _ (der_76572 v h) (by intro d hd; cases hd)))
def cl_79662 : CNF.NClause := [(16,false),(9,false),(75,true)]
theorem der_79662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79662 :=
  CNF.rup_sound cl_79662 [cl_77265,cl_76633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77265 v h) (hints_cons _ _ _ (der_76633 v h) (by intro d hd; cases hd)))
def cl_79663 : CNF.NClause := [(26,false),(22,false),(75,true)]
theorem der_79663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79663 :=
  CNF.rup_sound cl_79663 [cl_50175,cl_76652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50175 v h) (hints_cons _ _ _ (der_76652 v h) (by intro d hd; cases hd)))
def cl_79664 : CNF.NClause := [(15,false),(78,true),(13,false)]
theorem der_79664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79664 :=
  CNF.rup_sound cl_79664 [cl_50181,cl_76646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50181 v h) (hints_cons _ _ _ (der_76646 v h) (by intro d hd; cases hd)))
def cl_79665 : CNF.NClause := [(6,false),(13,false),(78,true)]
theorem der_79665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79665 :=
  CNF.rup_sound cl_79665 [cl_57852,cl_76929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57852 v h) (hints_cons _ _ _ (der_76929 v h) (by intro d hd; cases hd)))
def cl_79666 : CNF.NClause := [(83,true),(23,false),(4,false)]
theorem der_79666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79666 :=
  CNF.rup_sound cl_79666 [cl_77269,cl_54211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77269 v h) (hints_cons _ _ _ (der_54211 v h) (by intro d hd; cases hd)))
def cl_79667 : CNF.NClause := [(10,false),(76,true),(24,false)]
theorem der_79667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79667 :=
  CNF.rup_sound cl_79667 [cl_77271,cl_76592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77271 v h) (hints_cons _ _ _ (der_76592 v h) (by intro d hd; cases hd)))
def cl_79668 : CNF.NClause := [(15,false),(6,false),(78,true)]
theorem der_79668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79668 :=
  CNF.rup_sound cl_79668 [cl_50194,cl_76647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50194 v h) (hints_cons _ _ _ (der_76647 v h) (by intro d hd; cases hd)))
def cl_79669 : CNF.NClause := [(22,false),(6,false),(78,true)]
theorem der_79669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79669 :=
  CNF.rup_sound cl_79669 [cl_50202,cl_76930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50202 v h) (hints_cons _ _ _ (der_76930 v h) (by intro d hd; cases hd)))
def cl_79670 : CNF.NClause := [(1,false),(19,false),(71,true)]
theorem der_79670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79670 :=
  CNF.rup_sound cl_79670 [cl_77272,cl_76588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77272 v h) (hints_cons _ _ _ (der_76588 v h) (by intro d hd; cases hd)))
def cl_79671 : CNF.NClause := [(1,false),(7,false),(71,true)]
theorem der_79671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79671 :=
  CNF.rup_sound cl_79671 [cl_50203,cl_79670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50203 v h) (hints_cons _ _ _ (der_79670 v h) (by intro d hd; cases hd)))
def cl_79672 : CNF.NClause := [(11,false),(18,false),(69,true)]
theorem der_79672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79672 :=
  CNF.rup_sound cl_79672 [cl_50206,cl_76915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50206 v h) (hints_cons _ _ _ (der_76915 v h) (by intro d hd; cases hd)))
def cl_79673 : CNF.NClause := [(10,false),(21,false),(73,true)]
theorem der_79673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79673 :=
  CNF.rup_sound cl_79673 [cl_50215,cl_76902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50215 v h) (hints_cons _ _ _ (der_76902 v h) (by intro d hd; cases hd)))
def cl_79674 : CNF.NClause := [(97,true),(32,false),(47,false)]
theorem der_79674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79674 :=
  CNF.rup_sound cl_79674 [cl_77343,cl_76658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77343 v h) (hints_cons _ _ _ (der_76658 v h) (by intro d hd; cases hd)))
def cl_79675 : CNF.NClause := [(64,true),(53,false),(22,true)]
theorem der_79675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79675 :=
  CNF.rup_sound cl_79675 [cl_77380,cl_79505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77380 v h) (hints_cons _ _ _ (der_79505 v h) (by intro d hd; cases hd)))
def cl_79676 : CNF.NClause := [(118,true),(34,false),(32,false)]
theorem der_79676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79676 :=
  CNF.rup_sound cl_79676 [cl_77401,cl_76704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77401 v h) (hints_cons _ _ _ (der_76704 v h) (by intro d hd; cases hd)))
def cl_79677 : CNF.NClause := [(103,true),(42,false),(44,false)]
theorem der_79677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79677 :=
  CNF.rup_sound cl_79677 [cl_77407,cl_76709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77407 v h) (hints_cons _ _ _ (der_76709 v h) (by intro d hd; cases hd)))
def cl_79678 : CNF.NClause := [(50,false),(94,true),(55,false)]
theorem der_79678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79678 :=
  CNF.rup_sound cl_79678 [cl_77409,cl_76998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77409 v h) (hints_cons _ _ _ (der_76998 v h) (by intro d hd; cases hd)))
def cl_79679 : CNF.NClause := [(40,false),(94,true),(55,false)]
theorem der_79679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79679 :=
  CNF.rup_sound cl_79679 [cl_77410,cl_76761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77410 v h) (hints_cons _ _ _ (der_76761 v h) (by intro d hd; cases hd)))
def cl_79680 : CNF.NClause := [(94,true),(50,false),(40,false)]
theorem der_79680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79680 :=
  CNF.rup_sound cl_79680 [cl_77411,cl_76923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77411 v h) (hints_cons _ _ _ (der_76923 v h) (by intro d hd; cases hd)))
def cl_79681 : CNF.NClause := [(102,true),(32,false),(51,false)]
theorem der_79681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79681 :=
  CNF.rup_sound cl_79681 [cl_44369,cl_76975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44369 v h) (hints_cons _ _ _ (der_76975 v h) (by intro d hd; cases hd)))
def cl_79682 : CNF.NClause := [(102,true),(51,false),(44,false)]
theorem der_79682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79682 :=
  CNF.rup_sound cl_79682 [cl_50376,cl_76850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50376 v h) (hints_cons _ _ _ (der_76850 v h) (by intro d hd; cases hd)))
def cl_79684 : CNF.NClause := [(113,true),(39,false),(36,false)]
theorem der_79684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79684 :=
  CNF.rup_sound cl_79684 [cl_77424,cl_76895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77424 v h) (hints_cons _ _ _ (der_76895 v h) (by intro d hd; cases hd)))
def cl_79685 : CNF.NClause := [(14,false),(70,true),(28,false)]
theorem der_79685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79685 :=
  CNF.rup_sound cl_79685 [cl_77426,cl_76621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77426 v h) (hints_cons _ _ _ (der_76621 v h) (by intro d hd; cases hd)))
def cl_79686 : CNF.NClause := [(75,true),(9,false),(26,false)]
theorem der_79686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79686 :=
  CNF.rup_sound cl_79686 [cl_77427,cl_49815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77427 v h) (hints_cons _ _ _ (der_49815 v h) (by intro d hd; cases hd)))
def cl_79687 : CNF.NClause := [(49,false),(86,false),(18,true)]
theorem der_79687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79687 :=
  CNF.rup_sound cl_79687 [cl_58995,cl_79466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58995 v h) (hints_cons _ _ _ (der_79466 v h) (by intro d hd; cases hd)))
def cl_79688 : CNF.NClause := [(107,true),(48,false),(41,false)]
theorem der_79688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79688 :=
  CNF.rup_sound cl_79688 [cl_77443,cl_76772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77443 v h) (hints_cons _ _ _ (der_76772 v h) (by intro d hd; cases hd)))
def cl_79689 : CNF.NClause := [(102,true),(32,false),(51,false)]
theorem der_79689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79689 :=
  CNF.rup_sound cl_79689 [cl_77445,cl_76767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77445 v h) (hints_cons _ _ _ (der_76767 v h) (by intro d hd; cases hd)))
def cl_79690 : CNF.NClause := [(34,false),(116,true),(36,false)]
theorem der_79690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79690 :=
  CNF.rup_sound cl_79690 [cl_77447,cl_76808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77447 v h) (hints_cons _ _ _ (der_76808 v h) (by intro d hd; cases hd)))
def cl_79692 : CNF.NClause := [(84,true),(152,false),(2,true)]
theorem der_79692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79692 :=
  CNF.rup_sound cl_79692 [cl_77450,cl_15793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77450 v h) (hints_cons _ _ _ (der_15793 v h) (by intro d hd; cases hd)))
def cl_79693 : CNF.NClause := [(34,false),(116,true),(58,false)]
theorem der_79693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79693 :=
  CNF.rup_sound cl_79693 [cl_77453,cl_76672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77453 v h) (hints_cons _ _ _ (der_76672 v h) (by intro d hd; cases hd)))
def cl_79695 : CNF.NClause := [(102,true),(50,false),(51,false)]
theorem der_79695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79695 :=
  CNF.rup_sound cl_79695 [cl_77466,cl_76767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77466 v h) (hints_cons _ _ _ (der_76767 v h) (by intro d hd; cases hd)))
def cl_79696 : CNF.NClause := [(234,true),(17,false),(70,true)]
theorem der_79696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79696 :=
  CNF.rup_sound cl_79696 [cl_77468,cl_54024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77468 v h) (hints_cons _ _ _ (der_54024 v h) (by intro d hd; cases hd)))
def cl_79697 : CNF.NClause := [(72,true),(44,false),(78,false)]
theorem der_79697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79697 :=
  CNF.rup_sound cl_79697 [cl_49673,cl_79473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49673 v h) (hints_cons _ _ _ (der_79473 v h) (by intro d hd; cases hd)))
def cl_79699 : CNF.NClause := [(75,true),(134,false),(3,true)]
theorem der_79699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79699 :=
  CNF.rup_sound cl_79699 [cl_77470,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77470 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_79701 : CNF.NClause := [(49,false),(73,true),(18,true)]
theorem der_79701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79701 :=
  CNF.rup_sound cl_79701 [cl_49719,cl_79687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49719 v h) (hints_cons _ _ _ (der_79687 v h) (by intro d hd; cases hd)))
def cl_79702 : CNF.NClause := [(57,false),(26,true),(79,false)]
theorem der_79702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79702 :=
  CNF.rup_sound cl_79702 [cl_49554,cl_79508] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49554 v h) (hints_cons _ _ _ (der_79508 v h) (by intro d hd; cases hd)))
def cl_79703 : CNF.NClause := [(43,false),(103,true),(41,false)]
theorem der_79703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79703 :=
  CNF.rup_sound cl_79703 [cl_77494,cl_76730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77494 v h) (hints_cons _ _ _ (der_76730 v h) (by intro d hd; cases hd)))
def cl_79704 : CNF.NClause := [(75,true),(140,false),(127,true)]
theorem der_79704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79704 :=
  CNF.rup_sound cl_79704 [cl_77496,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77496 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_79705 : CNF.NClause := [(45,false),(103,true),(43,false)]
theorem der_79705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79705 :=
  CNF.rup_sound cl_79705 [cl_77498,cl_76729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77498 v h) (hints_cons _ _ _ (der_76729 v h) (by intro d hd; cases hd)))
def cl_79709 : CNF.NClause := [(927,false),(7,true),(73,true)]
theorem der_79709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79709 :=
  CNF.rup_sound cl_79709 [cl_77510,cl_62084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77510 v h) (hints_cons _ _ _ (der_62084 v h) (by intro d hd; cases hd)))
def cl_79710 : CNF.NClause := [(83,true),(4,false),(5,false)]
theorem der_79710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79710 :=
  CNF.rup_sound cl_79710 [cl_77517,cl_62292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77517 v h) (hints_cons _ _ _ (der_62292 v h) (by intro d hd; cases hd)))
def cl_79713 : CNF.NClause := [(83,true),(4,false),(26,false)]
theorem der_79713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79713 :=
  CNF.rup_sound cl_79713 [cl_77527,cl_79710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77527 v h) (hints_cons _ _ _ (der_79710 v h) (by intro d hd; cases hd)))
def cl_79715 : CNF.NClause := [(920,true),(921,false),(67,true)]
theorem der_79715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79715 :=
  CNF.rup_sound cl_79715 [cl_77530,cl_62078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77530 v h) (hints_cons _ _ _ (der_62078 v h) (by intro d hd; cases hd)))
def cl_79716 : CNF.NClause := [(2,false),(69,true),(27,false)]
theorem der_79716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79716 :=
  CNF.rup_sound cl_79716 [cl_77535,cl_39879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77535 v h) (hints_cons _ _ _ (der_39879 v h) (by intro d hd; cases hd)))
def cl_79717 : CNF.NClause := [(83,true),(4,false),(17,false)]
theorem der_79717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79717 :=
  CNF.rup_sound cl_79717 [cl_77536,cl_76960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77536 v h) (hints_cons _ _ _ (der_76960 v h) (by intro d hd; cases hd)))
def cl_79718 : CNF.NClause := [(133,false),(82,true),(88,false)]
theorem der_79718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79718 :=
  CNF.rup_sound cl_79718 [cl_77542,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77542 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_79719 : CNF.NClause := [(920,false),(922,true),(67,true)]
theorem der_79719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79719 :=
  CNF.rup_sound cl_79719 [cl_77543,cl_62077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77543 v h) (hints_cons _ _ _ (der_62077 v h) (by intro d hd; cases hd)))
def cl_79721 : CNF.NClause := [(132,false),(90,false),(39,true)]
theorem der_79721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79721 :=
  CNF.rup_sound cl_79721 [cl_77547,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77547 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_79722 : CNF.NClause := [(148,false),(80,true),(135,true)]
theorem der_79722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79722 :=
  CNF.rup_sound cl_79722 [cl_77550,cl_72318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77550 v h) (hints_cons _ _ _ (der_72318 v h) (by intro d hd; cases hd)))
def cl_79724 : CNF.NClause := [(88,true),(78,false),(44,false)]
theorem der_79724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79724 :=
  CNF.rup_sound cl_79724 [cl_77554,cl_79473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77554 v h) (hints_cons _ _ _ (der_79473 v h) (by intro d hd; cases hd)))
def cl_79725 : CNF.NClause := [(26,true),(57,false),(91,false)]
theorem der_79725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79725 :=
  CNF.rup_sound cl_79725 [cl_79507,cl_79510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79507 v h) (hints_cons _ _ _ (der_79510 v h) (by intro d hd; cases hd)))
def cl_79726 : CNF.NClause := [(40,false),(82,true),(9,true)]
theorem der_79726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79726 :=
  CNF.rup_sound cl_79726 [cl_79530,cl_79532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79530 v h) (hints_cons _ _ _ (der_79532 v h) (by intro d hd; cases hd)))
def cl_79727 : CNF.NClause := [(43,false),(81,false),(12,true)]
theorem der_79727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79727 :=
  CNF.rup_sound cl_79727 [cl_79556,cl_79557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79556 v h) (hints_cons _ _ _ (der_79557 v h) (by intro d hd; cases hd)))
def cl_79729 : CNF.NClause := [(46,false),(79,false),(78,false),(77,true)]
theorem der_79729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79729 :=
  CNF.rup_sound cl_79729 [cl_77565,cl_79537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77565 v h) (hints_cons _ _ _ (der_79537 v h) (by intro d hd; cases hd)))
def cl_79730 : CNF.NClause := [(82,false),(76,true),(90,false),(39,false)]
theorem der_79730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79730 :=
  CNF.rup_sound cl_79730 [cl_77573,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77573 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_79731 : CNF.NClause := [(65,true),(82,false),(39,false),(90,false)]
theorem der_79731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79731 :=
  CNF.rup_sound cl_79731 [cl_77574,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77574 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_79734 : CNF.NClause := [(82,true),(39,false),(65,false),(76,false)]
theorem der_79734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79734 :=
  CNF.rup_sound cl_79734 [cl_77582,cl_77031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77582 v h) (hints_cons _ _ _ (der_77031 v h) (by intro d hd; cases hd)))
def cl_79735 : CNF.NClause := [(82,true),(76,false),(90,false),(39,false)]
theorem der_79735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79735 :=
  CNF.rup_sound cl_79735 [cl_77583,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77583 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_79736 : CNF.NClause := [(76,true),(68,false),(90,false),(39,false)]
theorem der_79736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79736 :=
  CNF.rup_sound cl_79736 [cl_77585,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77585 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_79737 : CNF.NClause := [(76,true),(90,false),(65,false),(39,false)]
theorem der_79737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79737 :=
  CNF.rup_sound cl_79737 [cl_42425,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42425 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_79738 : CNF.NClause := [(76,true),(90,false),(39,false),(79,false)]
theorem der_79738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79738 :=
  CNF.rup_sound cl_79738 [cl_77587,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77587 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79741 : CNF.NClause := [(90,false),(39,false),(65,false),(82,true)]
theorem der_79741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79741 :=
  CNF.rup_sound cl_79741 [cl_77594,cl_60245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77594 v h) (hints_cons _ _ _ (der_60245 v h) (by intro d hd; cases hd)))
def cl_79746 : CNF.NClause := [(90,true),(82,false),(65,false),(39,false)]
theorem der_79746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79746 :=
  CNF.rup_sound cl_79746 [cl_77597,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77597 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_79747 : CNF.NClause := [(65,true),(82,false),(39,false),(79,false)]
theorem der_79747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79747 :=
  CNF.rup_sound cl_79747 [cl_50611,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50611 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79749 : CNF.NClause := [(82,false),(68,false),(90,true),(39,false)]
theorem der_79749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79749 :=
  CNF.rup_sound cl_79749 [cl_77606,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77606 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79752 : CNF.NClause := [(65,true),(76,false),(39,false),(79,false)]
theorem der_79752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79752 :=
  CNF.rup_sound cl_79752 [cl_50617,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50617 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79753 : CNF.NClause := [(90,true),(39,false),(65,false),(8,false)]
theorem der_79753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79753 :=
  CNF.rup_sound cl_79753 [cl_77611,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77611 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_79754 : CNF.NClause := [(65,true),(68,false),(39,false),(79,false)]
theorem der_79754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79754 :=
  CNF.rup_sound cl_79754 [cl_50619,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50619 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79755 : CNF.NClause := [(90,true),(68,false),(39,false),(79,true)]
theorem der_79755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79755 :=
  CNF.rup_sound cl_79755 [cl_77614,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77614 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79756 : CNF.NClause := [(90,true),(39,false),(68,false),(65,false)]
theorem der_79756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79756 :=
  CNF.rup_sound cl_79756 [cl_50628,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50628 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_79759 : CNF.NClause := [(70,true),(6,false),(91,false),(37,false)]
theorem der_79759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79759 :=
  CNF.rup_sound cl_79759 [cl_50647,cl_77627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50647 v h) (hints_cons _ _ _ (der_77627 v h) (by intro d hd; cases hd)))
def cl_79760 : CNF.NClause := [(82,false),(78,false),(37,false),(66,true)]
theorem der_79760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79760 :=
  CNF.rup_sound cl_79760 [cl_50651,cl_77632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50651 v h) (hints_cons _ _ _ (der_77632 v h) (by intro d hd; cases hd)))
def cl_79761 : CNF.NClause := [(66,false),(78,true),(82,false),(37,false)]
theorem der_79761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79761 :=
  CNF.rup_sound cl_79761 [cl_77635,cl_50550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77635 v h) (hints_cons _ _ _ (der_50550 v h) (by intro d hd; cases hd)))
def cl_79762 : CNF.NClause := [(37,false),(74,false),(70,true),(78,false)]
theorem der_79762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79762 :=
  CNF.rup_sound cl_79762 [cl_77637,cl_79563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77637 v h) (hints_cons _ _ _ (der_79563 v h) (by intro d hd; cases hd)))
def cl_79763 : CNF.NClause := [(66,false),(70,false),(37,false),(78,true)]
theorem der_79763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79763 :=
  CNF.rup_sound cl_79763 [cl_77640,cl_79761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77640 v h) (hints_cons _ _ _ (der_79761 v h) (by intro d hd; cases hd)))
def cl_79764 : CNF.NClause := [(92,false),(85,true),(86,false),(36,false)]
theorem der_79764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79764 :=
  CNF.rup_sound cl_79764 [cl_50678,cl_79515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50678 v h) (hints_cons _ _ _ (der_79515 v h) (by intro d hd; cases hd)))
def cl_79765 : CNF.NClause := [(92,false),(82,false),(36,false),(85,true)]
theorem der_79765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79765 :=
  CNF.rup_sound cl_79765 [cl_77659,cl_79764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77659 v h) (hints_cons _ _ _ (der_79764 v h) (by intro d hd; cases hd)))
def cl_79766 : CNF.NClause := [(83,true),(92,false),(36,false),(85,true)]
theorem der_79766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79766 :=
  CNF.rup_sound cl_79766 [cl_50683,cl_79765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50683 v h) (hints_cons _ _ _ (der_79765 v h) (by intro d hd; cases hd)))
def cl_79767 : CNF.NClause := [(82,true),(83,true),(86,false),(36,false)]
theorem der_79767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79767 :=
  CNF.rup_sound cl_79767 [cl_77668,cl_79515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77668 v h) (hints_cons _ _ _ (der_79515 v h) (by intro d hd; cases hd)))
def cl_79768 : CNF.NClause := [(86,true),(85,false),(36,false),(84,false)]
theorem der_79768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79768 :=
  CNF.rup_sound cl_79768 [cl_77669,cl_79516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77669 v h) (hints_cons _ _ _ (der_79516 v h) (by intro d hd; cases hd)))
def cl_79770 : CNF.NClause := [(84,true),(85,false),(36,false),(83,false)]
theorem der_79770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79770 :=
  CNF.rup_sound cl_79770 [cl_77671,cl_79516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77671 v h) (hints_cons _ _ _ (der_79516 v h) (by intro d hd; cases hd)))
def cl_79772 : CNF.NClause := [(85,true),(84,false),(36,false),(82,false)]
theorem der_79772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79772 :=
  CNF.rup_sound cl_79772 [cl_77676,cl_77674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77676 v h) (hints_cons _ _ _ (der_77674 v h) (by intro d hd; cases hd)))
def cl_79773 : CNF.NClause := [(83,true),(36,false),(85,true),(84,false)]
theorem der_79773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79773 :=
  CNF.rup_sound cl_79773 [cl_50701,cl_79772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50701 v h) (hints_cons _ _ _ (der_79772 v h) (by intro d hd; cases hd)))
def cl_79774 : CNF.NClause := [(84,true),(92,true),(36,false),(83,false)]
theorem der_79774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79774 :=
  CNF.rup_sound cl_79774 [cl_77680,cl_79770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77680 v h) (hints_cons _ _ _ (der_79770 v h) (by intro d hd; cases hd)))
def cl_79775 : CNF.NClause := [(85,false),(78,false),(58,false),(69,true)]
theorem der_79775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79775 :=
  CNF.rup_sound cl_79775 [cl_77698,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77698 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79776 : CNF.NClause := [(62,false),(85,true),(58,false),(89,false)]
theorem der_79776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79776 :=
  CNF.rup_sound cl_79776 [cl_77707,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77707 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79778 : CNF.NClause := [(89,true),(85,false),(58,false),(76,false)]
theorem der_79778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79778 :=
  CNF.rup_sound cl_79778 [cl_77723,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77723 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79779 : CNF.NClause := [(62,false),(78,true),(58,false),(85,false)]
theorem der_79779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79779 :=
  CNF.rup_sound cl_79779 [cl_50753,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50753 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79780 : CNF.NClause := [(85,true),(76,false),(58,false),(78,false)]
theorem der_79780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79780 :=
  CNF.rup_sound cl_79780 [cl_77728,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77728 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79781 : CNF.NClause := [(76,false),(58,false),(69,true),(78,false)]
theorem der_79781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79781 :=
  CNF.rup_sound cl_79781 [cl_50755,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50755 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79782 : CNF.NClause := [(69,false),(76,true),(78,false),(58,false)]
theorem der_79782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79782 :=
  CNF.rup_sound cl_79782 [cl_50758,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50758 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79783 : CNF.NClause := [(62,true),(76,true),(78,false),(58,false)]
theorem der_79783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79783 :=
  CNF.rup_sound cl_79783 [cl_50760,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50760 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79784 : CNF.NClause := [(78,true),(76,false),(69,false),(58,false)]
theorem der_79784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79784 :=
  CNF.rup_sound cl_79784 [cl_77732,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77732 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79787 : CNF.NClause := [(85,true),(58,false),(76,false),(69,true)]
theorem der_79787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79787 :=
  CNF.rup_sound cl_79787 [cl_50765,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50765 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79788 : CNF.NClause := [(62,false),(78,true),(58,false),(69,false)]
theorem der_79788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79788 :=
  CNF.rup_sound cl_79788 [cl_50766,cl_79502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50766 v h) (hints_cons _ _ _ (der_79502 v h) (by intro d hd; cases hd)))
def cl_79790 : CNF.NClause := [(54,false),(89,false),(74,true),(23,false)]
theorem der_79790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79790 :=
  CNF.rup_sound cl_79790 [cl_77743,cl_57003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77743 v h) (hints_cons _ _ _ (der_57003 v h) (by intro d hd; cases hd)))
def cl_79791 : CNF.NClause := [(83,true),(89,false),(81,false),(54,false)]
theorem der_79791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79791 :=
  CNF.rup_sound cl_79791 [cl_77749,cl_79487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77749 v h) (hints_cons _ _ _ (der_79487 v h) (by intro d hd; cases hd)))
def cl_79792 : CNF.NClause := [(65,true),(67,true),(54,false),(89,false)]
theorem der_79792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79792 :=
  CNF.rup_sound cl_79792 [cl_77751,cl_79582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77751 v h) (hints_cons _ _ _ (der_79582 v h) (by intro d hd; cases hd)))
def cl_79793 : CNF.NClause := [(65,true),(74,false),(54,false),(89,false)]
theorem der_79793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79793 :=
  CNF.rup_sound cl_79793 [cl_50775,cl_79792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50775 v h) (hints_cons _ _ _ (der_79792 v h) (by intro d hd; cases hd)))
def cl_79794 : CNF.NClause := [(83,true),(54,false),(23,false),(89,false)]
theorem der_79794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79794 :=
  CNF.rup_sound cl_79794 [cl_77753,cl_57003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77753 v h) (hints_cons _ _ _ (der_57003 v h) (by intro d hd; cases hd)))
def cl_79795 : CNF.NClause := [(54,false),(67,true),(89,false),(74,false)]
theorem der_79795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79795 :=
  CNF.rup_sound cl_79795 [cl_50776,cl_79792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50776 v h) (hints_cons _ _ _ (der_79792 v h) (by intro d hd; cases hd)))
def cl_79796 : CNF.NClause := [(81,false),(54,false),(74,true),(23,false)]
theorem der_79796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79796 :=
  CNF.rup_sound cl_79796 [cl_77759,cl_79487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77759 v h) (hints_cons _ _ _ (der_79487 v h) (by intro d hd; cases hd)))
def cl_79797 : CNF.NClause := [(67,false),(81,true),(23,false),(54,false)]
theorem der_79797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79797 :=
  CNF.rup_sound cl_79797 [cl_77763,cl_56354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77763 v h) (hints_cons _ _ _ (der_56354 v h) (by intro d hd; cases hd)))
def cl_79798 : CNF.NClause := [(74,false),(65,false),(54,false),(81,true)]
theorem der_79798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79798 :=
  CNF.rup_sound cl_79798 [cl_77765,cl_79583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77765 v h) (hints_cons _ _ _ (der_79583 v h) (by intro d hd; cases hd)))
def cl_79799 : CNF.NClause := [(83,false),(74,false),(67,true),(54,false)]
theorem der_79799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79799 :=
  CNF.rup_sound cl_79799 [cl_50785,cl_79795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50785 v h) (hints_cons _ _ _ (der_79795 v h) (by intro d hd; cases hd)))
def cl_79800 : CNF.NClause := [(67,false),(54,false),(83,false),(81,true)]
theorem der_79800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79800 :=
  CNF.rup_sound cl_79800 [cl_50787,cl_77764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50787 v h) (hints_cons _ _ _ (der_77764 v h) (by intro d hd; cases hd)))
def cl_79801 : CNF.NClause := [(83,false),(67,true),(65,true),(54,false)]
theorem der_79801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79801 :=
  CNF.rup_sound cl_79801 [cl_50789,cl_79792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50789 v h) (hints_cons _ _ _ (der_79792 v h) (by intro d hd; cases hd)))
def cl_79802 : CNF.NClause := [(65,false),(74,false),(89,true),(54,false)]
theorem der_79802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79802 :=
  CNF.rup_sound cl_79802 [cl_77769,cl_79798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77769 v h) (hints_cons _ _ _ (der_79798 v h) (by intro d hd; cases hd)))
def cl_79803 : CNF.NClause := [(81,false),(54,false),(74,true),(65,false)]
theorem der_79803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79803 :=
  CNF.rup_sound cl_79803 [cl_50793,cl_79487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50793 v h) (hints_cons _ _ _ (der_79487 v h) (by intro d hd; cases hd)))
def cl_79804 : CNF.NClause := [(83,true),(81,false),(54,false),(65,false)]
theorem der_79804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79804 :=
  CNF.rup_sound cl_79804 [cl_50796,cl_79791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50796 v h) (hints_cons _ _ _ (der_79791 v h) (by intro d hd; cases hd)))
def cl_79805 : CNF.NClause := [(83,true),(54,false),(67,false),(74,false)]
theorem der_79805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79805 :=
  CNF.rup_sound cl_79805 [cl_50800,cl_77773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50800 v h) (hints_cons _ _ _ (der_77773 v h) (by intro d hd; cases hd)))
def cl_79806 : CNF.NClause := [(65,false),(54,false),(74,false),(67,true)]
theorem der_79806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79806 :=
  CNF.rup_sound cl_79806 [cl_50801,cl_79583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50801 v h) (hints_cons _ _ _ (der_79583 v h) (by intro d hd; cases hd)))
def cl_79807 : CNF.NClause := [(74,false),(54,false),(67,true),(23,false)]
theorem der_79807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79807 :=
  CNF.rup_sound cl_79807 [cl_50803,cl_77737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50803 v h) (hints_cons _ _ _ (der_77737 v h) (by intro d hd; cases hd)))
def cl_79808 : CNF.NClause := [(89,true),(74,false),(67,true),(54,false)]
theorem der_79808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79808 :=
  CNF.rup_sound cl_79808 [cl_50804,cl_79806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50804 v h) (hints_cons _ _ _ (der_79806 v h) (by intro d hd; cases hd)))
def cl_79809 : CNF.NClause := [(63,true),(69,false),(82,false),(40,false)]
theorem der_79809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79809 :=
  CNF.rup_sound cl_79809 [cl_77776,cl_79532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77776 v h) (hints_cons _ _ _ (der_79532 v h) (by intro d hd; cases hd)))
def cl_79810 : CNF.NClause := [(63,true),(81,false),(40,false),(88,false)]
theorem der_79810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79810 :=
  CNF.rup_sound cl_79810 [cl_77777,cl_79475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77777 v h) (hints_cons _ _ _ (der_79475 v h) (by intro d hd; cases hd)))
def cl_79811 : CNF.NClause := [(63,true),(82,false),(40,false),(88,false)]
theorem der_79811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79811 :=
  CNF.rup_sound cl_79811 [cl_77778,cl_79476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77778 v h) (hints_cons _ _ _ (der_79476 v h) (by intro d hd; cases hd)))
def cl_79813 : CNF.NClause := [(81,true),(88,false),(82,false),(40,false)]
theorem der_79813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79813 :=
  CNF.rup_sound cl_79813 [cl_77782,cl_79811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77782 v h) (hints_cons _ _ _ (der_79811 v h) (by intro d hd; cases hd)))
def cl_79814 : CNF.NClause := [(82,true),(81,false),(40,false),(88,false)]
theorem der_79814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79814 :=
  CNF.rup_sound cl_79814 [cl_77786,cl_79810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77786 v h) (hints_cons _ _ _ (der_79810 v h) (by intro d hd; cases hd)))
def cl_79817 : CNF.NClause := [(63,false),(88,false),(40,false),(69,true)]
theorem der_79817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79817 :=
  CNF.rup_sound cl_79817 [cl_50830,cl_77081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50830 v h) (hints_cons _ _ _ (der_77081 v h) (by intro d hd; cases hd)))
def cl_79818 : CNF.NClause := [(63,false),(81,true),(40,false),(88,false)]
theorem der_79818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79818 :=
  CNF.rup_sound cl_79818 [cl_77790,cl_79475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77790 v h) (hints_cons _ _ _ (der_79475 v h) (by intro d hd; cases hd)))
def cl_79819 : CNF.NClause := [(81,true),(88,false),(40,false),(69,false)]
theorem der_79819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79819 :=
  CNF.rup_sound cl_79819 [cl_77791,cl_79532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77791 v h) (hints_cons _ _ _ (der_79532 v h) (by intro d hd; cases hd)))
def cl_79820 : CNF.NClause := [(9,false),(40,false),(88,false),(69,true)]
theorem der_79820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79820 :=
  CNF.rup_sound cl_79820 [cl_77792,cl_79817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77792 v h) (hints_cons _ _ _ (der_79817 v h) (by intro d hd; cases hd)))
def cl_79822 : CNF.NClause := [(9,false),(63,true),(40,false),(88,false)]
theorem der_79822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79822 :=
  CNF.rup_sound cl_79822 [cl_77793,cl_79820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77793 v h) (hints_cons _ _ _ (der_79820 v h) (by intro d hd; cases hd)))
def cl_79823 : CNF.NClause := [(88,true),(75,false),(40,false),(82,false)]
theorem der_79823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79823 :=
  CNF.rup_sound cl_79823 [cl_77796,cl_79476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77796 v h) (hints_cons _ _ _ (der_79476 v h) (by intro d hd; cases hd)))
def cl_79824 : CNF.NClause := [(75,false),(82,false),(69,true),(40,false)]
theorem der_79824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79824 :=
  CNF.rup_sound cl_79824 [cl_77797,cl_79476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77797 v h) (hints_cons _ _ _ (der_79476 v h) (by intro d hd; cases hd)))
def cl_79825 : CNF.NClause := [(75,true),(40,false),(69,false),(82,false)]
theorem der_79825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79825 :=
  CNF.rup_sound cl_79825 [cl_77798,cl_79809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77798 v h) (hints_cons _ _ _ (der_79809 v h) (by intro d hd; cases hd)))
def cl_79826 : CNF.NClause := [(63,false),(40,false),(82,false),(69,true)]
theorem der_79826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79826 :=
  CNF.rup_sound cl_79826 [cl_50841,cl_77081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50841 v h) (hints_cons _ _ _ (der_77081 v h) (by intro d hd; cases hd)))
def cl_79828 : CNF.NClause := [(88,true),(82,false),(69,true),(40,false)]
theorem der_79828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79828 :=
  CNF.rup_sound cl_79828 [cl_50842,cl_79476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50842 v h) (hints_cons _ _ _ (der_79476 v h) (by intro d hd; cases hd)))
def cl_79831 : CNF.NClause := [(63,false),(75,false),(69,true),(40,false)]
theorem der_79831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79831 :=
  CNF.rup_sound cl_79831 [cl_50852,cl_77081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50852 v h) (hints_cons _ _ _ (der_77081 v h) (by intro d hd; cases hd)))
def cl_79832 : CNF.NClause := [(82,true),(81,false),(40,false),(69,false)]
theorem der_79832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79832 :=
  CNF.rup_sound cl_79832 [cl_77806,cl_79726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77806 v h) (hints_cons _ _ _ (der_79726 v h) (by intro d hd; cases hd)))
def cl_79833 : CNF.NClause := [(9,false),(81,false),(63,true),(40,false)]
theorem der_79833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79833 :=
  CNF.rup_sound cl_79833 [cl_77807,cl_79810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77807 v h) (hints_cons _ _ _ (der_79810 v h) (by intro d hd; cases hd)))
def cl_79834 : CNF.NClause := [(63,false),(40,false),(81,false),(82,true)]
theorem der_79834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79834 :=
  CNF.rup_sound cl_79834 [cl_77809,cl_79726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77809 v h) (hints_cons _ _ _ (der_79726 v h) (by intro d hd; cases hd)))
def cl_79836 : CNF.NClause := [(63,true),(40,false),(69,true),(81,false)]
theorem der_79836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79836 :=
  CNF.rup_sound cl_79836 [cl_50855,cl_79810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50855 v h) (hints_cons _ _ _ (der_79810 v h) (by intro d hd; cases hd)))
def cl_79837 : CNF.NClause := [(88,true),(63,false),(40,false),(75,false)]
theorem der_79837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79837 :=
  CNF.rup_sound cl_79837 [cl_77811,cl_79831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77811 v h) (hints_cons _ _ _ (der_79831 v h) (by intro d hd; cases hd)))
def cl_79840 : CNF.NClause := [(68,false),(60,false),(74,true),(88,false)]
theorem der_79840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79840 :=
  CNF.rup_sound cl_79840 [cl_50863,cl_79585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50863 v h) (hints_cons _ _ _ (der_79585 v h) (by intro d hd; cases hd)))
def cl_79842 : CNF.NClause := [(86,false),(60,false),(80,false),(74,true)]
theorem der_79842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79842 :=
  CNF.rup_sound cl_79842 [cl_77837,cl_77836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77837 v h) (hints_cons _ _ _ (der_77836 v h) (by intro d hd; cases hd)))
def cl_79843 : CNF.NClause := [(60,false),(62,true),(68,false),(80,false)]
theorem der_79843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79843 :=
  CNF.rup_sound cl_79843 [cl_77850,cl_77846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77850 v h) (hints_cons _ _ _ (der_77846 v h) (by intro d hd; cases hd)))
def cl_79844 : CNF.NClause := [(86,true),(80,false),(60,false),(62,true)]
theorem der_79844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79844 :=
  CNF.rup_sound cl_79844 [cl_77854,cl_79843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77854 v h) (hints_cons _ _ _ (der_79843 v h) (by intro d hd; cases hd)))
def cl_79845 : CNF.NClause := [(62,true),(68,false),(74,false),(60,false)]
theorem der_79845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79845 :=
  CNF.rup_sound cl_79845 [cl_77857,cl_79843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77857 v h) (hints_cons _ _ _ (der_79843 v h) (by intro d hd; cases hd)))
def cl_79846 : CNF.NClause := [(86,true),(74,false),(68,true),(60,false)]
theorem der_79846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79846 :=
  CNF.rup_sound cl_79846 [cl_50868,cl_77848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50868 v h) (hints_cons _ _ _ (der_77848 v h) (by intro d hd; cases hd)))
def cl_79847 : CNF.NClause := [(62,false),(60,false),(68,false),(74,true)]
theorem der_79847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79847 :=
  CNF.rup_sound cl_79847 [cl_77859,cl_77841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77859 v h) (hints_cons _ _ _ (der_77841 v h) (by intro d hd; cases hd)))
def cl_79848 : CNF.NClause := [(91,false),(84,false),(55,false),(80,true)]
theorem der_79848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79848 :=
  CNF.rup_sound cl_79848 [cl_77870,cl_79541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77870 v h) (hints_cons _ _ _ (der_79541 v h) (by intro d hd; cases hd)))
def cl_79851 : CNF.NClause := [(63,true),(76,false),(91,false),(55,false)]
theorem der_79851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79851 :=
  CNF.rup_sound cl_79851 [cl_50874,cl_77877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50874 v h) (hints_cons _ _ _ (der_77877 v h) (by intro d hd; cases hd)))
def cl_79852 : CNF.NClause := [(63,false),(91,false),(55,false),(76,true)]
theorem der_79852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79852 :=
  CNF.rup_sound cl_79852 [cl_50876,cl_79545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50876 v h) (hints_cons _ _ _ (der_79545 v h) (by intro d hd; cases hd)))
def cl_79853 : CNF.NClause := [(63,true),(76,false),(84,false),(55,false)]
theorem der_79853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79853 :=
  CNF.rup_sound cl_79853 [cl_77891,cl_77863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77891 v h) (hints_cons _ _ _ (der_77863 v h) (by intro d hd; cases hd)))
def cl_79854 : CNF.NClause := [(63,false),(84,false),(55,false),(67,true)]
theorem der_79854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79854 :=
  CNF.rup_sound cl_79854 [cl_50884,cl_79545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50884 v h) (hints_cons _ _ _ (der_79545 v h) (by intro d hd; cases hd)))
def cl_79855 : CNF.NClause := [(76,false),(80,false),(67,true),(55,false)]
theorem der_79855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79855 :=
  CNF.rup_sound cl_79855 [cl_77899,cl_79542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77899 v h) (hints_cons _ _ _ (der_79542 v h) (by intro d hd; cases hd)))
def cl_79857 : CNF.NClause := [(63,false),(80,false),(55,false),(67,true)]
theorem der_79857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79857 :=
  CNF.rup_sound cl_79857 [cl_77904,cl_79855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77904 v h) (hints_cons _ _ _ (der_79855 v h) (by intro d hd; cases hd)))
def cl_79858 : CNF.NClause := [(63,true),(67,false),(55,false),(76,false)]
theorem der_79858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79858 :=
  CNF.rup_sound cl_79858 [cl_50890,cl_77877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50890 v h) (hints_cons _ _ _ (der_77877 v h) (by intro d hd; cases hd)))
def cl_79860 : CNF.NClause := [(63,true),(67,false),(80,true),(55,false)]
theorem der_79860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79860 :=
  CNF.rup_sound cl_79860 [cl_50895,cl_79858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50895 v h) (hints_cons _ _ _ (der_79858 v h) (by intro d hd; cases hd)))
def cl_79862 : CNF.NClause := [(78,true),(46,false),(81,false),(77,false)]
theorem der_79862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79862 :=
  CNF.rup_sound cl_79862 [cl_77913,cl_79539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77913 v h) (hints_cons _ _ _ (der_79539 v h) (by intro d hd; cases hd)))
def cl_79863 : CNF.NClause := [(78,true),(81,false),(92,false),(46,false)]
theorem der_79863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79863 :=
  CNF.rup_sound cl_79863 [cl_77917,cl_79862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77917 v h) (hints_cons _ _ _ (der_79862 v h) (by intro d hd; cases hd)))
def cl_79864 : CNF.NClause := [(15,false),(78,true),(46,false),(92,false)]
theorem der_79864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79864 :=
  CNF.rup_sound cl_79864 [cl_77926,cl_79863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77926 v h) (hints_cons _ _ _ (der_79863 v h) (by intro d hd; cases hd)))
def cl_79865 : CNF.NClause := [(15,false),(92,false),(80,true),(46,false)]
theorem der_79865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79865 :=
  CNF.rup_sound cl_79865 [cl_77927,cl_79864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77927 v h) (hints_cons _ _ _ (der_79864 v h) (by intro d hd; cases hd)))
def cl_79866 : CNF.NClause := [(78,true),(80,false),(46,false),(81,false)]
theorem der_79866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79866 :=
  CNF.rup_sound cl_79866 [cl_50912,cl_79539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50912 v h) (hints_cons _ _ _ (der_79539 v h) (by intro d hd; cases hd)))
def cl_79867 : CNF.NClause := [(92,true),(46,false),(77,false),(81,false)]
theorem der_79867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79867 :=
  CNF.rup_sound cl_79867 [cl_77933,cl_79539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77933 v h) (hints_cons _ _ _ (der_79539 v h) (by intro d hd; cases hd)))
def cl_79868 : CNF.NClause := [(77,true),(46,false),(78,false),(81,false)]
theorem der_79868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79868 :=
  CNF.rup_sound cl_79868 [cl_77935,cl_79539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77935 v h) (hints_cons _ _ _ (der_79539 v h) (by intro d hd; cases hd)))
def cl_79869 : CNF.NClause := [(92,true),(46,false),(81,false),(78,false)]
theorem der_79869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79869 :=
  CNF.rup_sound cl_79869 [cl_77936,cl_79867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77936 v h) (hints_cons _ _ _ (der_79867 v h) (by intro d hd; cases hd)))
def cl_79871 : CNF.NClause := [(78,true),(79,false),(46,false),(80,false)]
theorem der_79871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79871 :=
  CNF.rup_sound cl_79871 [cl_77938,cl_79537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77938 v h) (hints_cons _ _ _ (der_79537 v h) (by intro d hd; cases hd)))
def cl_79873 : CNF.NClause := [(77,true),(46,false),(78,false),(80,false)]
theorem der_79873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79873 :=
  CNF.rup_sound cl_79873 [cl_77941,cl_79540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77941 v h) (hints_cons _ _ _ (der_79540 v h) (by intro d hd; cases hd)))
def cl_79875 : CNF.NClause := [(81,true),(79,false),(46,false),(78,false)]
theorem der_79875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79875 :=
  CNF.rup_sound cl_79875 [cl_77942,cl_79537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77942 v h) (hints_cons _ _ _ (der_79537 v h) (by intro d hd; cases hd)))
def cl_79876 : CNF.NClause := [(46,false),(78,true),(77,false),(79,false)]
theorem der_79876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79876 :=
  CNF.rup_sound cl_79876 [cl_50926,cl_79537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50926 v h) (hints_cons _ _ _ (der_79537 v h) (by intro d hd; cases hd)))
def cl_79877 : CNF.NClause := [(46,false),(15,false),(79,false),(78,true)]
theorem der_79877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79877 :=
  CNF.rup_sound cl_79877 [cl_77943,cl_79864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77943 v h) (hints_cons _ _ _ (der_79864 v h) (by intro d hd; cases hd)))
def cl_79881 : CNF.NClause := [(87,false),(80,false),(34,false),(3,true)]
theorem der_79881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79881 :=
  CNF.rup_sound cl_79881 [cl_37388,cl_79574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37388 v h) (hints_cons _ _ _ (der_79574 v h) (by intro d hd; cases hd)))
def cl_79882 : CNF.NClause := [(75,true),(34,false),(87,false),(85,false)]
theorem der_79882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79882 :=
  CNF.rup_sound cl_79882 [cl_77985,cl_79573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77985 v h) (hints_cons _ _ _ (der_79573 v h) (by intro d hd; cases hd)))
def cl_79883 : CNF.NClause := [(34,false),(87,false),(85,false),(80,true)]
theorem der_79883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79883 :=
  CNF.rup_sound cl_79883 [cl_50961,cl_79882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50961 v h) (hints_cons _ _ _ (der_79882 v h) (by intro d hd; cases hd)))
def cl_79884 : CNF.NClause := [(34,false),(87,false),(75,false),(65,true)]
theorem der_79884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79884 :=
  CNF.rup_sound cl_79884 [cl_77991,cl_79572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77991 v h) (hints_cons _ _ _ (der_79572 v h) (by intro d hd; cases hd)))
def cl_79885 : CNF.NClause := [(34,false),(87,false),(75,false),(80,true)]
theorem der_79885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79885 :=
  CNF.rup_sound cl_79885 [cl_77996,cl_79884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77996 v h) (hints_cons _ _ _ (der_79884 v h) (by intro d hd; cases hd)))
def cl_79886 : CNF.NClause := [(87,false),(75,true),(34,false),(70,true)]
theorem der_79886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79886 :=
  CNF.rup_sound cl_79886 [cl_50975,cl_79882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50975 v h) (hints_cons _ _ _ (der_79882 v h) (by intro d hd; cases hd)))
def cl_79887 : CNF.NClause := [(75,true),(34,false),(85,false),(80,false)]
theorem der_79887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79887 :=
  CNF.rup_sound cl_79887 [cl_78002,cl_79573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78002 v h) (hints_cons _ _ _ (der_79573 v h) (by intro d hd; cases hd)))
def cl_79888 : CNF.NClause := [(75,true),(85,false),(34,false),(70,true)]
theorem der_79888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79888 :=
  CNF.rup_sound cl_79888 [cl_78005,cl_79573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78005 v h) (hints_cons _ _ _ (der_79573 v h) (by intro d hd; cases hd)))
def cl_79889 : CNF.NClause := [(65,true),(75,false),(34,false),(70,false)]
theorem der_79889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79889 :=
  CNF.rup_sound cl_79889 [cl_78007,cl_79572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78007 v h) (hints_cons _ _ _ (der_79572 v h) (by intro d hd; cases hd)))
def cl_79890 : CNF.NClause := [(75,true),(34,false),(65,false),(85,false)]
theorem der_79890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79890 :=
  CNF.rup_sound cl_79890 [cl_78009,cl_79573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78009 v h) (hints_cons _ _ _ (der_79573 v h) (by intro d hd; cases hd)))
def cl_79892 : CNF.NClause := [(75,true),(34,false),(80,true),(85,false)]
theorem der_79892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79892 :=
  CNF.rup_sound cl_79892 [cl_78011,cl_79890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78011 v h) (hints_cons _ _ _ (der_79890 v h) (by intro d hd; cases hd)))
def cl_79893 : CNF.NClause := [(34,false),(75,false),(70,false),(85,true)]
theorem der_79893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79893 :=
  CNF.rup_sound cl_79893 [cl_78013,cl_79571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78013 v h) (hints_cons _ _ _ (der_79571 v h) (by intro d hd; cases hd)))
def cl_79894 : CNF.NClause := [(3,false),(85,true),(34,false),(75,false)]
theorem der_79894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79894 :=
  CNF.rup_sound cl_79894 [cl_78017,cl_79893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78017 v h) (hints_cons _ _ _ (der_79893 v h) (by intro d hd; cases hd)))
def cl_79895 : CNF.NClause := [(80,false),(34,false),(65,true),(85,true)]
theorem der_79895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79895 :=
  CNF.rup_sound cl_79895 [cl_50983,cl_79572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50983 v h) (hints_cons _ _ _ (der_79572 v h) (by intro d hd; cases hd)))
def cl_79896 : CNF.NClause := [(70,false),(75,false),(80,true),(34,false)]
theorem der_79896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79896 :=
  CNF.rup_sound cl_79896 [cl_50984,cl_79889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50984 v h) (hints_cons _ _ _ (der_79889 v h) (by intro d hd; cases hd)))
def cl_79897 : CNF.NClause := [(65,true),(34,false),(80,true),(75,false)]
theorem der_79897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79897 :=
  CNF.rup_sound cl_79897 [cl_50989,cl_79889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50989 v h) (hints_cons _ _ _ (der_79889 v h) (by intro d hd; cases hd)))
def cl_79898 : CNF.NClause := [(87,true),(80,true),(34,false),(75,true)]
theorem der_79898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79898 :=
  CNF.rup_sound cl_79898 [cl_78021,cl_79892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78021 v h) (hints_cons _ _ _ (der_79892 v h) (by intro d hd; cases hd)))
def cl_79899 : CNF.NClause := [(34,false),(85,true),(65,true),(70,false)]
theorem der_79899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79899 :=
  CNF.rup_sound cl_79899 [cl_50990,cl_79572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50990 v h) (hints_cons _ _ _ (der_79572 v h) (by intro d hd; cases hd)))
def cl_79900 : CNF.NClause := [(65,true),(70,false),(34,false),(80,true)]
theorem der_79900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79900 :=
  CNF.rup_sound cl_79900 [cl_78022,cl_79889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78022 v h) (hints_cons _ _ _ (der_79889 v h) (by intro d hd; cases hd)))
def cl_79902 : CNF.NClause := [(48,false),(88,false),(76,true),(83,false)]
theorem der_79902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79902 :=
  CNF.rup_sound cl_79902 [cl_78024,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78024 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_79905 : CNF.NClause := [(83,true),(77,false),(48,false),(88,false)]
theorem der_79905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79905 :=
  CNF.rup_sound cl_79905 [cl_51010,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51010 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_79913 : CNF.NClause := [(64,false),(48,false),(83,false),(76,true)]
theorem der_79913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79913 :=
  CNF.rup_sound cl_79913 [cl_78044,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78044 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_79914 : CNF.NClause := [(77,true),(48,false),(76,false),(83,false)]
theorem der_79914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79914 :=
  CNF.rup_sound cl_79914 [cl_78046,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78046 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_79916 : CNF.NClause := [(77,true),(64,false),(83,false),(48,false)]
theorem der_79916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79916 :=
  CNF.rup_sound cl_79916 [cl_51021,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51021 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_79918 : CNF.NClause := [(70,true),(77,false),(76,false),(48,false)]
theorem der_79918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79918 :=
  CNF.rup_sound cl_79918 [cl_78050,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78050 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_79920 : CNF.NClause := [(64,false),(70,true),(77,false),(48,false)]
theorem der_79920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79920 :=
  CNF.rup_sound cl_79920 [cl_51026,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51026 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_79927 : CNF.NClause := [(91,false),(85,false),(43,false),(68,true)]
theorem der_79927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79927 :=
  CNF.rup_sound cl_79927 [cl_78068,cl_79484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78068 v h) (hints_cons _ _ _ (der_79484 v h) (by intro d hd; cases hd)))
def cl_79928 : CNF.NClause := [(72,true),(85,false),(43,false),(91,false)]
theorem der_79928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79928 :=
  CNF.rup_sound cl_79928 [cl_78069,cl_79927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78069 v h) (hints_cons _ _ _ (der_79927 v h) (by intro d hd; cases hd)))
def cl_79930 : CNF.NClause := [(64,true),(81,false),(91,false),(43,false)]
theorem der_79930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79930 :=
  CNF.rup_sound cl_79930 [cl_78074,cl_79727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78074 v h) (hints_cons _ _ _ (der_79727 v h) (by intro d hd; cases hd)))
def cl_79931 : CNF.NClause := [(91,false),(68,true),(43,false),(81,false)]
theorem der_79931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79931 :=
  CNF.rup_sound cl_79931 [cl_51041,cl_79727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51041 v h) (hints_cons _ _ _ (der_79727 v h) (by intro d hd; cases hd)))
def cl_79935 : CNF.NClause := [(91,false),(81,true),(68,false),(43,false)]
theorem der_79935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79935 :=
  CNF.rup_sound cl_79935 [cl_78080,cl_79461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78080 v h) (hints_cons _ _ _ (der_79461 v h) (by intro d hd; cases hd)))
def cl_79936 : CNF.NClause := [(43,false),(68,true),(72,false),(81,false)]
theorem der_79936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79936 :=
  CNF.rup_sound cl_79936 [cl_78081,cl_79727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78081 v h) (hints_cons _ _ _ (der_79727 v h) (by intro d hd; cases hd)))
def cl_79937 : CNF.NClause := [(72,true),(43,false),(81,false),(85,false)]
theorem der_79937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79937 :=
  CNF.rup_sound cl_79937 [cl_78084,cl_79557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78084 v h) (hints_cons _ _ _ (der_79557 v h) (by intro d hd; cases hd)))
def cl_79940 : CNF.NClause := [(43,false),(64,false),(68,false),(81,true)]
theorem der_79940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79940 :=
  CNF.rup_sound cl_79940 [cl_78085,cl_79461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78085 v h) (hints_cons _ _ _ (der_79461 v h) (by intro d hd; cases hd)))
def cl_79942 : CNF.NClause := [(72,true),(43,false),(68,false),(85,false)]
theorem der_79942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79942 :=
  CNF.rup_sound cl_79942 [cl_78087,cl_79461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78087 v h) (hints_cons _ _ _ (der_79461 v h) (by intro d hd; cases hd)))
def cl_79944 : CNF.NClause := [(72,true),(43,false),(85,false),(68,true)]
theorem der_79944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79944 :=
  CNF.rup_sound cl_79944 [cl_51064,cl_79484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51064 v h) (hints_cons _ _ _ (der_79484 v h) (by intro d hd; cases hd)))
def cl_79945 : CNF.NClause := [(85,true),(43,false),(81,false),(72,false)]
theorem der_79945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79945 :=
  CNF.rup_sound cl_79945 [cl_78088,cl_79936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78088 v h) (hints_cons _ _ _ (der_79936 v h) (by intro d hd; cases hd)))
def cl_79949 : CNF.NClause := [(43,false),(68,true),(81,false),(12,false)]
theorem der_79949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79949 :=
  CNF.rup_sound cl_79949 [cl_51072,cl_79936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51072 v h) (hints_cons _ _ _ (der_79936 v h) (by intro d hd; cases hd)))
def cl_79951 : CNF.NClause := [(64,false),(43,false),(72,false),(85,true)]
theorem der_79951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79951 :=
  CNF.rup_sound cl_79951 [cl_78093,cl_79945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78093 v h) (hints_cons _ _ _ (der_79945 v h) (by intro d hd; cases hd)))
def cl_79952 : CNF.NClause := [(72,true),(64,false),(43,false),(81,true)]
theorem der_79952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79952 :=
  CNF.rup_sound cl_79952 [cl_51081,cl_79940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51081 v h) (hints_cons _ _ _ (der_79940 v h) (by intro d hd; cases hd)))
def cl_79953 : CNF.NClause := [(64,false),(84,false),(33,false),(79,true)]
theorem der_79953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79953 :=
  CNF.rup_sound cl_79953 [cl_78100,cl_79477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78100 v h) (hints_cons _ _ _ (der_79477 v h) (by intro d hd; cases hd)))
def cl_79954 : CNF.NClause := [(87,false),(33,false),(84,false),(79,true)]
theorem der_79954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79954 :=
  CNF.rup_sound cl_79954 [cl_78101,cl_79477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78101 v h) (hints_cons _ _ _ (der_79477 v h) (by intro d hd; cases hd)))
def cl_79955 : CNF.NClause := [(64,true),(87,false),(84,false),(33,false)]
theorem der_79955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79955 :=
  CNF.rup_sound cl_79955 [cl_51084,cl_79477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51084 v h) (hints_cons _ _ _ (der_79477 v h) (by intro d hd; cases hd)))
def cl_79957 : CNF.NClause := [(84,true),(87,false),(33,false),(79,false)]
theorem der_79957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79957 :=
  CNF.rup_sound cl_79957 [cl_78103,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78103 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_79958 : CNF.NClause := [(64,true),(87,false),(33,false),(79,false)]
theorem der_79958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79958 :=
  CNF.rup_sound cl_79958 [cl_78104,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78104 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_79960 : CNF.NClause := [(87,false),(64,false),(33,false),(74,true)]
theorem der_79960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79960 :=
  CNF.rup_sound cl_79960 [cl_78107,cl_77472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78107 v h) (hints_cons _ _ _ (der_77472 v h) (by intro d hd; cases hd)))
def cl_79961 : CNF.NClause := [(79,true),(87,false),(33,false),(64,false)]
theorem der_79961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79961 :=
  CNF.rup_sound cl_79961 [cl_51090,cl_79960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51090 v h) (hints_cons _ _ _ (der_79960 v h) (by intro d hd; cases hd)))
def cl_79963 : CNF.NClause := [(87,true),(33,false),(84,false),(79,false)]
theorem der_79963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79963 :=
  CNF.rup_sound cl_79963 [cl_78109,cl_79477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78109 v h) (hints_cons _ _ _ (der_79477 v h) (by intro d hd; cases hd)))
def cl_79964 : CNF.NClause := [(64,true),(33,false),(79,false),(84,false)]
theorem der_79964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79964 :=
  CNF.rup_sound cl_79964 [cl_78110,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78110 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_79966 : CNF.NClause := [(2,false),(84,false),(79,true),(33,false)]
theorem der_79966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79966 :=
  CNF.rup_sound cl_79966 [cl_51105,cl_79477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51105 v h) (hints_cons _ _ _ (der_79477 v h) (by intro d hd; cases hd)))
def cl_79968 : CNF.NClause := [(84,true),(74,false),(33,false),(64,false)]
theorem der_79968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79968 :=
  CNF.rup_sound cl_79968 [cl_78114,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78114 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_79969 : CNF.NClause := [(64,true),(74,false),(33,false),(79,false)]
theorem der_79969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79969 :=
  CNF.rup_sound cl_79969 [cl_51112,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51112 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_79970 : CNF.NClause := [(64,false),(74,true),(79,false),(33,false)]
theorem der_79970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79970 :=
  CNF.rup_sound cl_79970 [cl_51117,cl_77472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51117 v h) (hints_cons _ _ _ (der_77472 v h) (by intro d hd; cases hd)))
def cl_79971 : CNF.NClause := [(2,false),(64,true),(33,false),(79,false)]
theorem der_79971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79971 :=
  CNF.rup_sound cl_79971 [cl_78115,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78115 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_79972 : CNF.NClause := [(84,true),(87,true),(33,false),(74,false)]
theorem der_79972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79972 :=
  CNF.rup_sound cl_79972 [cl_78116,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78116 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_79973 : CNF.NClause := [(38,false),(73,true),(82,false),(89,false)]
theorem der_79973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79973 :=
  CNF.rup_sound cl_79973 [cl_78121,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78121 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79974 : CNF.NClause := [(38,false),(64,true),(89,false),(82,false)]
theorem der_79974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79974 :=
  CNF.rup_sound cl_79974 [cl_78123,cl_77442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78123 v h) (hints_cons _ _ _ (der_77442 v h) (by intro d hd; cases hd)))
def cl_79976 : CNF.NClause := [(38,false),(73,false),(89,false),(71,true)]
theorem der_79976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79976 :=
  CNF.rup_sound cl_79976 [cl_78128,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78128 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79977 : CNF.NClause := [(38,false),(80,false),(89,false),(73,true)]
theorem der_79977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79977 :=
  CNF.rup_sound cl_79977 [cl_78131,cl_79973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78131 v h) (hints_cons _ _ _ (der_79973 v h) (by intro d hd; cases hd)))
def cl_79978 : CNF.NClause := [(38,false),(73,false),(80,true),(89,false)]
theorem der_79978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79978 :=
  CNF.rup_sound cl_79978 [cl_78133,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78133 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79979 : CNF.NClause := [(73,true),(71,false),(38,false),(89,false)]
theorem der_79979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79979 :=
  CNF.rup_sound cl_79979 [cl_78137,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78137 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79980 : CNF.NClause := [(64,false),(38,false),(89,false),(80,true)]
theorem der_79980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79980 :=
  CNF.rup_sound cl_79980 [cl_78138,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78138 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79982 : CNF.NClause := [(71,true),(38,false),(80,true),(89,false)]
theorem der_79982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79982 :=
  CNF.rup_sound cl_79982 [cl_78140,cl_79980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78140 v h) (hints_cons _ _ _ (der_79980 v h) (by intro d hd; cases hd)))
def cl_79983 : CNF.NClause := [(64,true),(38,false),(80,false),(82,false)]
theorem der_79983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79983 :=
  CNF.rup_sound cl_79983 [cl_51141,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51141 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79984 : CNF.NClause := [(64,true),(38,false),(73,false),(82,false)]
theorem der_79984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79984 :=
  CNF.rup_sound cl_79984 [cl_51143,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51143 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79986 : CNF.NClause := [(73,true),(71,false),(38,false),(82,false)]
theorem der_79986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79986 :=
  CNF.rup_sound cl_79986 [cl_78144,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78144 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79987 : CNF.NClause := [(64,true),(82,false),(71,false),(38,false)]
theorem der_79987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79987 :=
  CNF.rup_sound cl_79987 [cl_51145,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51145 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79988 : CNF.NClause := [(64,false),(38,false),(80,true),(82,false)]
theorem der_79988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79988 :=
  CNF.rup_sound cl_79988 [cl_51147,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51147 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79989 : CNF.NClause := [(82,true),(64,false),(38,false),(80,false)]
theorem der_79989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79989 :=
  CNF.rup_sound cl_79989 [cl_78149,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78149 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79990 : CNF.NClause := [(89,true),(71,false),(38,false),(64,true)]
theorem der_79990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79990 :=
  CNF.rup_sound cl_79990 [cl_78152,cl_79523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78152 v h) (hints_cons _ _ _ (der_79523 v h) (by intro d hd; cases hd)))
def cl_79992 : CNF.NClause := [(62,true),(90,false),(59,false),(84,false)]
theorem der_79992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79992 :=
  CNF.rup_sound cl_79992 [cl_78157,cl_79559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78157 v h) (hints_cons _ _ _ (der_79559 v h) (by intro d hd; cases hd)))
def cl_79993 : CNF.NClause := [(90,false),(59,false),(70,true),(84,false)]
theorem der_79993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79993 :=
  CNF.rup_sound cl_79993 [cl_78159,cl_79559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78159 v h) (hints_cons _ _ _ (der_79559 v h) (by intro d hd; cases hd)))
def cl_79994 : CNF.NClause := [(73,true),(84,false),(90,false),(59,false)]
theorem der_79994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79994 :=
  CNF.rup_sound cl_79994 [cl_78161,cl_79992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78161 v h) (hints_cons _ _ _ (der_79992 v h) (by intro d hd; cases hd)))
def cl_79996 : CNF.NClause := [(81,true),(90,false),(84,false),(59,false)]
theorem der_79996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79996 :=
  CNF.rup_sound cl_79996 [cl_78163,cl_78158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78163 v h) (hints_cons _ _ _ (der_78158 v h) (by intro d hd; cases hd)))
def cl_79997 : CNF.NClause := [(73,false),(28,true),(59,false),(70,false)]
theorem der_79997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79997 :=
  CNF.rup_sound cl_79997 [cl_45283,cl_79561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45283 v h) (hints_cons _ _ _ (der_79561 v h) (by intro d hd; cases hd)))
def cl_79998 : CNF.NClause := [(81,false),(73,true),(59,false),(90,false)]
theorem der_79998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79998 :=
  CNF.rup_sound cl_79998 [cl_78167,cl_79994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78167 v h) (hints_cons _ _ _ (der_79994 v h) (by intro d hd; cases hd)))
def cl_79999 : CNF.NClause := [(62,false),(59,false),(90,false),(81,true)]
theorem der_79999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_79999 :=
  CNF.rup_sound cl_79999 [cl_78168,cl_79561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78168 v h) (hints_cons _ _ _ (der_79561 v h) (by intro d hd; cases hd)))
def cl_80000 : CNF.NClause := [(28,false),(62,true),(90,false),(59,false)]
theorem der_80000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80000 :=
  CNF.rup_sound cl_80000 [cl_51170,cl_79482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51170 v h) (hints_cons _ _ _ (der_79482 v h) (by intro d hd; cases hd)))
def cl_80002 : CNF.NClause := [(81,false),(84,false),(73,true),(59,false)]
theorem der_80002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80002 :=
  CNF.rup_sound cl_80002 [cl_78173,cl_79559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78173 v h) (hints_cons _ _ _ (der_79559 v h) (by intro d hd; cases hd)))
def cl_80003 : CNF.NClause := [(81,false),(70,true),(59,false),(84,false)]
theorem der_80003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80003 :=
  CNF.rup_sound cl_80003 [cl_51179,cl_79559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51179 v h) (hints_cons _ _ _ (der_79559 v h) (by intro d hd; cases hd)))
def cl_80004 : CNF.NClause := [(62,false),(84,false),(73,true),(59,false)]
theorem der_80004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80004 :=
  CNF.rup_sound cl_80004 [cl_78175,cl_79559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78175 v h) (hints_cons _ _ _ (der_79559 v h) (by intro d hd; cases hd)))
def cl_80005 : CNF.NClause := [(70,false),(73,true),(59,false),(84,false)]
theorem der_80005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80005 :=
  CNF.rup_sound cl_80005 [cl_78176,cl_79559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78176 v h) (hints_cons _ _ _ (der_79559 v h) (by intro d hd; cases hd)))
def cl_80007 : CNF.NClause := [(81,true),(62,true),(84,false),(59,false)]
theorem der_80007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80007 :=
  CNF.rup_sound cl_80007 [cl_51186,cl_79559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51186 v h) (hints_cons _ _ _ (der_79559 v h) (by intro d hd; cases hd)))
def cl_80008 : CNF.NClause := [(73,false),(81,false),(59,false),(70,true)]
theorem der_80008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80008 :=
  CNF.rup_sound cl_80008 [cl_51190,cl_80003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51190 v h) (hints_cons _ _ _ (der_80003 v h) (by intro d hd; cases hd)))
def cl_80009 : CNF.NClause := [(62,false),(81,false),(59,false),(84,true)]
theorem der_80009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80009 :=
  CNF.rup_sound cl_80009 [cl_51191,cl_77142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51191 v h) (hints_cons _ _ _ (der_77142 v h) (by intro d hd; cases hd)))
def cl_80010 : CNF.NClause := [(62,true),(81,false),(73,true),(59,false)]
theorem der_80010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80010 :=
  CNF.rup_sound cl_80010 [cl_78183,cl_80002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78183 v h) (hints_cons _ _ _ (der_80002 v h) (by intro d hd; cases hd)))
def cl_80012 : CNF.NClause := [(75,false),(74,true),(41,false),(73,false)]
theorem der_80012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80012 :=
  CNF.rup_sound cl_80012 [cl_78195,cl_79462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78195 v h) (hints_cons _ _ _ (der_79462 v h) (by intro d hd; cases hd)))
def cl_80013 : CNF.NClause := [(92,false),(75,false),(74,true),(41,false)]
theorem der_80013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80013 :=
  CNF.rup_sound cl_80013 [cl_78196,cl_79462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78196 v h) (hints_cons _ _ _ (der_79462 v h) (by intro d hd; cases hd)))
def cl_80015 : CNF.NClause := [(75,false),(72,true),(76,false),(41,false)]
theorem der_80015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80015 :=
  CNF.rup_sound cl_80015 [cl_78207,cl_79462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78207 v h) (hints_cons _ _ _ (der_79462 v h) (by intro d hd; cases hd)))
def cl_80018 : CNF.NClause := [(74,false),(73,true),(41,false),(76,false)]
theorem der_80018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80018 :=
  CNF.rup_sound cl_80018 [cl_51240,cl_77452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51240 v h) (hints_cons _ _ _ (der_77452 v h) (by intro d hd; cases hd)))
def cl_80019 : CNF.NClause := [(92,true),(73,false),(41,false),(76,false)]
theorem der_80019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80019 :=
  CNF.rup_sound cl_80019 [cl_78212,cl_78205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78212 v h) (hints_cons _ _ _ (der_78205 v h) (by intro d hd; cases hd)))
def cl_80020 : CNF.NClause := [(75,true),(76,false),(41,false),(72,false)]
theorem der_80020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80020 :=
  CNF.rup_sound cl_80020 [cl_51244,cl_78189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51244 v h) (hints_cons _ _ _ (der_78189 v h) (by intro d hd; cases hd)))
def cl_80021 : CNF.NClause := [(72,true),(73,true),(76,false),(41,false)]
theorem der_80021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80021 :=
  CNF.rup_sound cl_80021 [cl_78213,cl_80018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78213 v h) (hints_cons _ _ _ (der_80018 v h) (by intro d hd; cases hd)))
def cl_80022 : CNF.NClause := [(75,false),(41,false),(73,false),(76,true)]
theorem der_80022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80022 :=
  CNF.rup_sound cl_80022 [cl_78214,cl_80012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78214 v h) (hints_cons _ _ _ (der_80012 v h) (by intro d hd; cases hd)))
def cl_80023 : CNF.NClause := [(75,false),(72,true),(74,false),(41,false)]
theorem der_80023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80023 :=
  CNF.rup_sound cl_80023 [cl_51248,cl_79462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51248 v h) (hints_cons _ _ _ (der_79462 v h) (by intro d hd; cases hd)))
def cl_80024 : CNF.NClause := [(41,false),(72,false),(74,true),(75,false)]
theorem der_80024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80024 :=
  CNF.rup_sound cl_80024 [cl_51253,cl_79462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51253 v h) (hints_cons _ _ _ (der_79462 v h) (by intro d hd; cases hd)))
def cl_80027 : CNF.NClause := [(73,false),(10,false),(41,false),(92,true)]
theorem der_80027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80027 :=
  CNF.rup_sound cl_80027 [cl_78217,cl_80019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78217 v h) (hints_cons _ _ _ (der_80019 v h) (by intro d hd; cases hd)))
def cl_80029 : CNF.NClause := [(74,false),(73,true),(41,false),(75,true)]
theorem der_80029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80029 :=
  CNF.rup_sound cl_80029 [cl_51263,cl_80018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51263 v h) (hints_cons _ _ _ (der_80018 v h) (by intro d hd; cases hd)))
def cl_80030 : CNF.NClause := [(92,true),(73,false),(74,true),(41,false)]
theorem der_80030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80030 :=
  CNF.rup_sound cl_80030 [cl_78219,cl_80019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78219 v h) (hints_cons _ _ _ (der_80019 v h) (by intro d hd; cases hd)))
def cl_80033 : CNF.NClause := [(63,false),(73,false),(68,true),(35,false)]
theorem der_80033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80033 :=
  CNF.rup_sound cl_80033 [cl_78236,cl_79480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78236 v h) (hints_cons _ _ _ (der_79480 v h) (by intro d hd; cases hd)))
def cl_80034 : CNF.NClause := [(35,false),(68,true),(78,false),(83,false)]
theorem der_80034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80034 :=
  CNF.rup_sound cl_80034 [cl_51292,cl_79577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51292 v h) (hints_cons _ _ _ (der_79577 v h) (by intro d hd; cases hd)))
def cl_80035 : CNF.NClause := [(63,true),(35,false),(68,false),(83,false)]
theorem der_80035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80035 :=
  CNF.rup_sound cl_80035 [cl_78247,cl_79578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78247 v h) (hints_cons _ _ _ (der_79578 v h) (by intro d hd; cases hd)))
def cl_80036 : CNF.NClause := [(78,true),(35,false),(83,false),(4,false)]
theorem der_80036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80036 :=
  CNF.rup_sound cl_80036 [cl_51299,cl_78245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51299 v h) (hints_cons _ _ _ (der_78245 v h) (by intro d hd; cases hd)))
def cl_80037 : CNF.NClause := [(63,true),(78,true),(83,false),(35,false)]
theorem der_80037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80037 :=
  CNF.rup_sound cl_80037 [cl_78248,cl_80035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78248 v h) (hints_cons _ _ _ (der_80035 v h) (by intro d hd; cases hd)))
def cl_80038 : CNF.NClause := [(83,true),(68,false),(35,false),(78,false)]
theorem der_80038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80038 :=
  CNF.rup_sound cl_80038 [cl_59959,cl_77161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59959 v h) (hints_cons _ _ _ (der_77161 v h) (by intro d hd; cases hd)))
def cl_80039 : CNF.NClause := [(63,true),(73,false),(35,false),(68,false)]
theorem der_80039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80039 :=
  CNF.rup_sound cl_80039 [cl_51300,cl_79480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51300 v h) (hints_cons _ _ _ (der_79480 v h) (by intro d hd; cases hd)))
def cl_80040 : CNF.NClause := [(63,false),(83,true),(35,false),(73,false)]
theorem der_80040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80040 :=
  CNF.rup_sound cl_80040 [cl_78249,cl_79480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78249 v h) (hints_cons _ _ _ (der_79480 v h) (by intro d hd; cases hd)))
def cl_80042 : CNF.NClause := [(63,true),(35,false),(68,false),(78,false)]
theorem der_80042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80042 :=
  CNF.rup_sound cl_80042 [cl_78251,cl_79578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78251 v h) (hints_cons _ _ _ (der_79578 v h) (by intro d hd; cases hd)))
def cl_80043 : CNF.NClause := [(63,false),(73,true),(78,false),(35,false)]
theorem der_80043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80043 :=
  CNF.rup_sound cl_80043 [cl_51304,cl_79577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51304 v h) (hints_cons _ _ _ (der_79577 v h) (by intro d hd; cases hd)))
def cl_80044 : CNF.NClause := [(63,true),(87,true),(35,false),(78,false)]
theorem der_80044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80044 :=
  CNF.rup_sound cl_80044 [cl_78252,cl_79577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78252 v h) (hints_cons _ _ _ (der_79577 v h) (by intro d hd; cases hd)))
def cl_80045 : CNF.NClause := [(63,false),(73,true),(35,false),(68,false)]
theorem der_80045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80045 :=
  CNF.rup_sound cl_80045 [cl_51310,cl_79578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51310 v h) (hints_cons _ _ _ (der_79578 v h) (by intro d hd; cases hd)))
def cl_80046 : CNF.NClause := [(63,true),(78,true),(68,false),(35,false)]
theorem der_80046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80046 :=
  CNF.rup_sound cl_80046 [cl_51312,cl_79578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51312 v h) (hints_cons _ _ _ (der_79578 v h) (by intro d hd; cases hd)))
def cl_80048 : CNF.NClause := [(63,false),(78,true),(68,true),(35,false)]
theorem der_80048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80048 :=
  CNF.rup_sound cl_80048 [cl_51314,cl_80033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51314 v h) (hints_cons _ _ _ (der_80033 v h) (by intro d hd; cases hd)))
def cl_80049 : CNF.NClause := [(69,false),(92,false),(51,false),(67,true)]
theorem der_80049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80049 :=
  CNF.rup_sound cl_80049 [cl_51383,cl_78288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51383 v h) (hints_cons _ _ _ (der_78288 v h) (by intro d hd; cases hd)))
def cl_80050 : CNF.NClause := [(92,false),(67,true),(71,true),(51,false)]
theorem der_80050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80050 :=
  CNF.rup_sound cl_80050 [cl_78295,cl_80049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78295 v h) (hints_cons _ _ _ (der_80049 v h) (by intro d hd; cases hd)))
def cl_80051 : CNF.NClause := [(69,false),(71,false),(68,true),(51,false)]
theorem der_80051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80051 :=
  CNF.rup_sound cl_80051 [cl_78306,cl_79567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78306 v h) (hints_cons _ _ _ (der_79567 v h) (by intro d hd; cases hd)))
def cl_80052 : CNF.NClause := [(68,false),(71,false),(67,true),(51,false)]
theorem der_80052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80052 :=
  CNF.rup_sound cl_80052 [cl_51395,cl_79566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51395 v h) (hints_cons _ _ _ (der_79566 v h) (by intro d hd; cases hd)))
def cl_80054 : CNF.NClause := [(70,true),(71,false),(69,true),(51,false)]
theorem der_80054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80054 :=
  CNF.rup_sound cl_80054 [cl_78309,cl_78307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78309 v h) (hints_cons _ _ _ (der_78307 v h) (by intro d hd; cases hd)))
def cl_80055 : CNF.NClause := [(70,false),(71,true),(51,false),(68,false)]
theorem der_80055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80055 :=
  CNF.rup_sound cl_80055 [cl_78310,cl_79565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78310 v h) (hints_cons _ _ _ (der_79565 v h) (by intro d hd; cases hd)))
def cl_80057 : CNF.NClause := [(71,true),(51,false),(67,false),(68,false)]
theorem der_80057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80057 :=
  CNF.rup_sound cl_80057 [cl_78318,cl_79564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78318 v h) (hints_cons _ _ _ (der_79564 v h) (by intro d hd; cases hd)))
def cl_80058 : CNF.NClause := [(71,true),(68,false),(69,false),(51,false)]
theorem der_80058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80058 :=
  CNF.rup_sound cl_80058 [cl_51406,cl_80057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51406 v h) (hints_cons _ _ _ (der_80057 v h) (by intro d hd; cases hd)))
def cl_80061 : CNF.NClause := [(92,true),(68,false),(20,true),(51,false)]
theorem der_80061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80061 :=
  CNF.rup_sound cl_80061 [cl_78321,cl_79566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78321 v h) (hints_cons _ _ _ (der_79566 v h) (by intro d hd; cases hd)))
def cl_80062 : CNF.NClause := [(20,false),(70,true),(69,true),(51,false)]
theorem der_80062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80062 :=
  CNF.rup_sound cl_80062 [cl_51414,cl_80054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51414 v h) (hints_cons _ _ _ (der_80054 v h) (by intro d hd; cases hd)))
def cl_80063 : CNF.NClause := [(63,true),(85,false),(74,false),(50,false)]
theorem der_80063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80063 :=
  CNF.rup_sound cl_80063 [cl_78325,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78325 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80064 : CNF.NClause := [(63,false),(71,true),(50,false),(90,false)]
theorem der_80064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80064 :=
  CNF.rup_sound cl_80064 [cl_78327,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78327 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80065 : CNF.NClause := [(85,false),(71,true),(90,false),(50,false)]
theorem der_80065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80065 :=
  CNF.rup_sound cl_80065 [cl_51418,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51418 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80067 : CNF.NClause := [(85,true),(77,false),(50,false),(90,false)]
theorem der_80067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80067 :=
  CNF.rup_sound cl_80067 [cl_78331,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78331 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80070 : CNF.NClause := [(63,false),(85,true),(50,false),(90,false)]
theorem der_80070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80070 :=
  CNF.rup_sound cl_80070 [cl_78335,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78335 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80071 : CNF.NClause := [(63,true),(77,true),(50,false),(90,false)]
theorem der_80071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80071 :=
  CNF.rup_sound cl_80071 [cl_78336,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78336 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80072 : CNF.NClause := [(63,false),(90,false),(50,false),(74,true)]
theorem der_80072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80072 :=
  CNF.rup_sound cl_80072 [cl_51428,cl_80064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51428 v h) (hints_cons _ _ _ (der_80064 v h) (by intro d hd; cases hd)))
def cl_80074 : CNF.NClause := [(85,false),(77,false),(74,true),(50,false)]
theorem der_80074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80074 :=
  CNF.rup_sound cl_80074 [cl_78341,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78341 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80075 : CNF.NClause := [(63,true),(85,false),(71,false),(50,false)]
theorem der_80075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80075 :=
  CNF.rup_sound cl_80075 [cl_51441,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51441 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80076 : CNF.NClause := [(77,true),(85,false),(63,false),(50,false)]
theorem der_80076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80076 :=
  CNF.rup_sound cl_80076 [cl_51443,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51443 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80077 : CNF.NClause := [(63,true),(85,false),(50,false),(90,true)]
theorem der_80077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80077 :=
  CNF.rup_sound cl_80077 [cl_51445,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51445 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80078 : CNF.NClause := [(63,true),(74,false),(77,false),(50,false)]
theorem der_80078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80078 :=
  CNF.rup_sound cl_80078 [cl_78345,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78345 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80080 : CNF.NClause := [(85,true),(63,false),(50,false),(77,false)]
theorem der_80080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80080 :=
  CNF.rup_sound cl_80080 [cl_78346,cl_79547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78346 v h) (hints_cons _ _ _ (der_79547 v h) (by intro d hd; cases hd)))
def cl_80083 : CNF.NClause := [(63,true),(19,false),(50,false),(74,false)]
theorem der_80083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80083 :=
  CNF.rup_sound cl_80083 [cl_78349,cl_77484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78349 v h) (hints_cons _ _ _ (der_77484 v h) (by intro d hd; cases hd)))
def cl_80088 : CNF.NClause := [(66,false),(87,false),(32,false),(71,true)]
theorem der_80088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80088 :=
  CNF.rup_sound cl_80088 [cl_78367,cl_78364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78367 v h) (hints_cons _ _ _ (der_78364 v h) (by intro d hd; cases hd)))
def cl_80089 : CNF.NClause := [(66,false),(76,true),(32,false),(86,false)]
theorem der_80089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80089 :=
  CNF.rup_sound cl_80089 [cl_78380,cl_78374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78380 v h) (hints_cons _ _ _ (der_78374 v h) (by intro d hd; cases hd)))
def cl_80090 : CNF.NClause := [(32,false),(86,false),(71,false),(87,true)]
theorem der_80090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80090 :=
  CNF.rup_sound cl_80090 [cl_78381,cl_79569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78381 v h) (hints_cons _ _ _ (der_79569 v h) (by intro d hd; cases hd)))
def cl_80091 : CNF.NClause := [(81,false),(32,false),(76,false),(1,true)]
theorem der_80091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80091 :=
  CNF.rup_sound cl_80091 [cl_78383,cl_79568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78383 v h) (hints_cons _ _ _ (der_79568 v h) (by intro d hd; cases hd)))
def cl_80092 : CNF.NClause := [(66,true),(76,false),(32,false),(81,false)]
theorem der_80092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80092 :=
  CNF.rup_sound cl_80092 [cl_51489,cl_80091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51489 v h) (hints_cons _ _ _ (der_80091 v h) (by intro d hd; cases hd)))
def cl_80093 : CNF.NClause := [(66,false),(1,false),(32,false),(76,true)]
theorem der_80093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80093 :=
  CNF.rup_sound cl_80093 [cl_78389,cl_80089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78389 v h) (hints_cons _ _ _ (der_80089 v h) (by intro d hd; cases hd)))
def cl_80094 : CNF.NClause := [(26,false),(83,true),(11,true),(17,false)]
theorem der_80094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80094 :=
  CNF.rup_sound cl_80094 [cl_30245,cl_79713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30245 v h) (hints_cons _ _ _ (der_79713 v h) (by intro d hd; cases hd)))
def cl_80095 : CNF.NClause := [(11,false),(26,true),(5,false),(83,true)]
theorem der_80095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80095 :=
  CNF.rup_sound cl_80095 [cl_78393,cl_54211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78393 v h) (hints_cons _ _ _ (der_54211 v h) (by intro d hd; cases hd)))
def cl_80097 : CNF.NClause := [(52,false),(67,false),(88,false),(85,true)]
theorem der_80097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80097 :=
  CNF.rup_sound cl_80097 [cl_78401,cl_79554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78401 v h) (hints_cons _ _ _ (der_79554 v h) (by intro d hd; cases hd)))
def cl_80098 : CNF.NClause := [(63,false),(70,true),(86,false),(45,false)]
theorem der_80098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80098 :=
  CNF.rup_sound cl_80098 [cl_51585,cl_78412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51585 v h) (hints_cons _ _ _ (der_78412 v h) (by intro d hd; cases hd)))
def cl_80099 : CNF.NClause := [(84,true),(47,false),(75,false),(77,false)]
theorem der_80099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80099 :=
  CNF.rup_sound cl_80099 [cl_78416,cl_79512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78416 v h) (hints_cons _ _ _ (der_79512 v h) (by intro d hd; cases hd)))
def cl_80100 : CNF.NClause := [(68,true),(77,false),(75,false),(47,false)]
theorem der_80100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80100 :=
  CNF.rup_sound cl_80100 [cl_51630,cl_80099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51630 v h) (hints_cons _ _ _ (der_80099 v h) (by intro d hd; cases hd)))
def cl_80101 : CNF.NClause := [(75,false),(68,false),(66,true),(47,false)]
theorem der_80101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80101 :=
  CNF.rup_sound cl_80101 [cl_78422,cl_79512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78422 v h) (hints_cons _ _ _ (der_79512 v h) (by intro d hd; cases hd)))
def cl_80102 : CNF.NClause := [(68,true),(47,false),(77,false),(89,true)]
theorem der_80102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80102 :=
  CNF.rup_sound cl_80102 [cl_78424,cl_80100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78424 v h) (hints_cons _ _ _ (der_80100 v h) (by intro d hd; cases hd)))
def cl_80103 : CNF.NClause := [(75,false),(68,false),(84,true),(47,false)]
theorem der_80103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80103 :=
  CNF.rup_sound cl_80103 [cl_51636,cl_79512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51636 v h) (hints_cons _ _ _ (der_79512 v h) (by intro d hd; cases hd)))
def cl_80106 : CNF.NClause := [(52,false),(73,false),(85,true),(67,false)]
theorem der_80106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80106 :=
  CNF.rup_sound cl_80106 [cl_78426,cl_79554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78426 v h) (hints_cons _ _ _ (der_79554 v h) (by intro d hd; cases hd)))
def cl_80108 : CNF.NClause := [(66,true),(77,false),(75,false),(47,false)]
theorem der_80108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80108 :=
  CNF.rup_sound cl_80108 [cl_51645,cl_80099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51645 v h) (hints_cons _ _ _ (der_80099 v h) (by intro d hd; cases hd)))
def cl_80109 : CNF.NClause := [(66,true),(88,false),(52,false),(67,false)]
theorem der_80109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80109 :=
  CNF.rup_sound cl_80109 [cl_51649,cl_80097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51649 v h) (hints_cons _ _ _ (der_80097 v h) (by intro d hd; cases hd)))
def cl_80114 : CNF.NClause := [(65,true),(44,false),(78,false),(84,false)]
theorem der_80114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80114 :=
  CNF.rup_sound cl_80114 [cl_78447,cl_79724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78447 v h) (hints_cons _ _ _ (der_79724 v h) (by intro d hd; cases hd)))
def cl_80115 : CNF.NClause := [(65,true),(88,false),(71,false),(44,false)]
theorem der_80115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80115 :=
  CNF.rup_sound cl_80115 [cl_78449,cl_79474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78449 v h) (hints_cons _ _ _ (der_79474 v h) (by intro d hd; cases hd)))
def cl_80118 : CNF.NClause := [(49,false),(86,true),(69,false),(77,false)]
theorem der_80118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80118 :=
  CNF.rup_sound cl_80118 [cl_51761,cl_77350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51761 v h) (hints_cons _ _ _ (der_77350 v h) (by intro d hd; cases hd)))
def cl_80119 : CNF.NClause := [(85,false),(73,true),(52,false),(67,false)]
theorem der_80119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80119 :=
  CNF.rup_sound cl_80119 [cl_78457,cl_79630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78457 v h) (hints_cons _ _ _ (der_79630 v h) (by intro d hd; cases hd)))
def cl_80120 : CNF.NClause := [(66,false),(52,false),(85,true),(67,false)]
theorem der_80120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80120 :=
  CNF.rup_sound cl_80120 [cl_78460,cl_79554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78460 v h) (hints_cons _ _ _ (der_79554 v h) (by intro d hd; cases hd)))
def cl_80122 : CNF.NClause := [(89,true),(47,false),(75,false),(77,false)]
theorem der_80122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80122 :=
  CNF.rup_sound cl_80122 [cl_78463,cl_79512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78463 v h) (hints_cons _ _ _ (der_79512 v h) (by intro d hd; cases hd)))
def cl_80123 : CNF.NClause := [(66,false),(89,true),(75,false),(47,false)]
theorem der_80123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80123 :=
  CNF.rup_sound cl_80123 [cl_40091,cl_79471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40091 v h) (hints_cons _ _ _ (der_79471 v h) (by intro d hd; cases hd)))
def cl_80124 : CNF.NClause := [(72,true),(88,false),(13,false),(44,false)]
theorem der_80124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80124 :=
  CNF.rup_sound cl_80124 [cl_78464,cl_79474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78464 v h) (hints_cons _ _ _ (der_79474 v h) (by intro d hd; cases hd)))
def cl_80127 : CNF.NClause := [(84,true),(78,true),(44,false),(72,false)]
theorem der_80127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80127 :=
  CNF.rup_sound cl_80127 [cl_78467,cl_79474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78467 v h) (hints_cons _ _ _ (der_79474 v h) (by intro d hd; cases hd)))
def cl_80128 : CNF.NClause := [(66,true),(89,false),(68,false),(47,false)]
theorem der_80128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80128 :=
  CNF.rup_sound cl_80128 [cl_78470,cl_60428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78470 v h) (hints_cons _ _ _ (der_60428 v h) (by intro d hd; cases hd)))
def cl_80129 : CNF.NClause := [(66,true),(77,false),(47,false),(68,false)]
theorem der_80129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80129 :=
  CNF.rup_sound cl_80129 [cl_51802,cl_78421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51802 v h) (hints_cons _ _ _ (der_78421 v h) (by intro d hd; cases hd)))
def cl_80130 : CNF.NClause := [(86,true),(64,false),(67,false),(53,false)]
theorem der_80130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80130 :=
  CNF.rup_sound cl_80130 [cl_78472,cl_77360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78472 v h) (hints_cons _ _ _ (der_77360 v h) (by intro d hd; cases hd)))
def cl_80133 : CNF.NClause := [(66,false),(77,true),(47,false),(84,false)]
theorem der_80133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80133 :=
  CNF.rup_sound cl_80133 [cl_51815,cl_77423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51815 v h) (hints_cons _ _ _ (der_77423 v h) (by intro d hd; cases hd)))
def cl_80134 : CNF.NClause := [(84,true),(47,false),(68,false),(89,false)]
theorem der_80134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80134 :=
  CNF.rup_sound cl_80134 [cl_51816,cl_80103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51816 v h) (hints_cons _ _ _ (der_80103 v h) (by intro d hd; cases hd)))
def cl_80135 : CNF.NClause := [(84,true),(66,false),(47,false),(68,false)]
theorem der_80135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80135 :=
  CNF.rup_sound cl_80135 [cl_51819,cl_80134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51819 v h) (hints_cons _ _ _ (der_80134 v h) (by intro d hd; cases hd)))
def cl_80136 : CNF.NClause := [(63,false),(86,true),(45,false),(70,false)]
theorem der_80136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_80136 :=
  CNF.rup_sound cl_80136 [cl_78480,cl_79457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78480 v h) (hints_cons _ _ _ (der_79457 v h) (by intro d hd; cases hd)))
def chunk078 : List CNF.NClause := [cl_79476,cl_79477,cl_79478,cl_79480,cl_79481,cl_79482,cl_79484,cl_79485,cl_79486,cl_79487,cl_79489,cl_79491,cl_79492,cl_79493,cl_79494,cl_79495,cl_79496,cl_79497,cl_79498,cl_79499,cl_79500,cl_79501,cl_79502,cl_79503,cl_79504,cl_79505,cl_79506,cl_79507,cl_79508,cl_79509,cl_79510,cl_79511,cl_79512,cl_79513,cl_79514,cl_79515,cl_79516,cl_79517,cl_79518,cl_79519,cl_79520,cl_79521,cl_79522,cl_79523,cl_79524,cl_79525,cl_79526,cl_79527,cl_79528,cl_79529,cl_79530,cl_79531,cl_79532,cl_79533,cl_79534,cl_79535,cl_79536,cl_79537,cl_79538,cl_79539,cl_79540,cl_79541,cl_79542,cl_79543,cl_79544,cl_79545,cl_79546,cl_79547,cl_79548,cl_79549,cl_79550,cl_79551,cl_79552,cl_79553,cl_79554,cl_79555,cl_79556,cl_79557,cl_79558,cl_79559,cl_79560,cl_79561,cl_79562,cl_79563,cl_79564,cl_79565,cl_79566,cl_79567,cl_79568,cl_79569,cl_79570,cl_79571,cl_79572,cl_79573,cl_79574,cl_79575,cl_79576,cl_79577,cl_79578,cl_79579,cl_79581,cl_79582,cl_79583,cl_79584,cl_79585,cl_79586,cl_79588,cl_79589,cl_79591,cl_79592,cl_79593,cl_79594,cl_79595,cl_79596,cl_79597,cl_79599,cl_79600,cl_79602,cl_79609,cl_79616,cl_79617,cl_79618,cl_79619,cl_79620,cl_79621,cl_79622,cl_79623,cl_79624,cl_79625,cl_79626,cl_79627,cl_79628,cl_79629,cl_79630,cl_79631,cl_79632,cl_79633,cl_79634,cl_79635,cl_79636,cl_79637,cl_79638,cl_79639,cl_79640,cl_79641,cl_79642,cl_79643,cl_79644,cl_79645,cl_79646,cl_79647,cl_79648,cl_79649,cl_79650,cl_79651,cl_79652,cl_79653,cl_79654,cl_79655,cl_79656,cl_79657,cl_79658,cl_79659,cl_79660,cl_79661,cl_79662,cl_79663,cl_79664,cl_79665,cl_79666,cl_79667,cl_79668,cl_79669,cl_79670,cl_79671,cl_79672,cl_79673,cl_79674,cl_79675,cl_79676,cl_79677,cl_79678,cl_79679,cl_79680,cl_79681,cl_79682,cl_79684,cl_79685,cl_79686,cl_79687,cl_79688,cl_79689,cl_79690,cl_79692,cl_79693,cl_79695,cl_79696,cl_79697,cl_79699,cl_79701,cl_79702,cl_79703,cl_79704,cl_79705,cl_79709,cl_79710,cl_79713,cl_79715,cl_79716,cl_79717,cl_79718,cl_79719,cl_79721,cl_79722,cl_79724,cl_79725,cl_79726,cl_79727,cl_79729,cl_79730,cl_79731,cl_79734,cl_79735,cl_79736,cl_79737,cl_79738,cl_79741,cl_79746,cl_79747,cl_79749,cl_79752,cl_79753,cl_79754,cl_79755,cl_79756,cl_79759,cl_79760,cl_79761,cl_79762,cl_79763,cl_79764,cl_79765,cl_79766,cl_79767,cl_79768,cl_79770,cl_79772,cl_79773,cl_79774,cl_79775,cl_79776,cl_79778,cl_79779,cl_79780,cl_79781,cl_79782,cl_79783,cl_79784,cl_79787,cl_79788,cl_79790,cl_79791,cl_79792,cl_79793,cl_79794,cl_79795,cl_79796,cl_79797,cl_79798,cl_79799,cl_79800,cl_79801,cl_79802,cl_79803,cl_79804,cl_79805,cl_79806,cl_79807,cl_79808,cl_79809,cl_79810,cl_79811,cl_79813,cl_79814,cl_79817,cl_79818,cl_79819,cl_79820,cl_79822,cl_79823,cl_79824,cl_79825,cl_79826,cl_79828,cl_79831,cl_79832,cl_79833,cl_79834,cl_79836,cl_79837,cl_79840,cl_79842,cl_79843,cl_79844,cl_79845,cl_79846,cl_79847,cl_79848,cl_79851,cl_79852,cl_79853,cl_79854,cl_79855,cl_79857,cl_79858,cl_79860,cl_79862,cl_79863,cl_79864,cl_79865,cl_79866,cl_79867,cl_79868,cl_79869,cl_79871,cl_79873,cl_79875,cl_79876,cl_79877,cl_79881,cl_79882,cl_79883,cl_79884,cl_79885,cl_79886,cl_79887,cl_79888,cl_79889,cl_79890,cl_79892,cl_79893,cl_79894,cl_79895,cl_79896,cl_79897,cl_79898,cl_79899,cl_79900,cl_79902,cl_79905,cl_79913,cl_79914,cl_79916,cl_79918,cl_79920,cl_79927,cl_79928,cl_79930,cl_79931,cl_79935,cl_79936,cl_79937,cl_79940,cl_79942,cl_79944,cl_79945,cl_79949,cl_79951,cl_79952,cl_79953,cl_79954,cl_79955,cl_79957,cl_79958,cl_79960,cl_79961,cl_79963,cl_79964,cl_79966,cl_79968,cl_79969,cl_79970,cl_79971,cl_79972,cl_79973,cl_79974,cl_79976,cl_79977,cl_79978,cl_79979,cl_79980,cl_79982,cl_79983,cl_79984,cl_79986,cl_79987,cl_79988,cl_79989,cl_79990,cl_79992,cl_79993,cl_79994,cl_79996,cl_79997,cl_79998,cl_79999,cl_80000,cl_80002,cl_80003,cl_80004,cl_80005,cl_80007,cl_80008,cl_80009,cl_80010,cl_80012,cl_80013,cl_80015,cl_80018,cl_80019,cl_80020,cl_80021,cl_80022,cl_80023,cl_80024,cl_80027,cl_80029,cl_80030,cl_80033,cl_80034,cl_80035,cl_80036,cl_80037,cl_80038,cl_80039,cl_80040,cl_80042,cl_80043,cl_80044,cl_80045,cl_80046,cl_80048,cl_80049,cl_80050,cl_80051,cl_80052,cl_80054,cl_80055,cl_80057,cl_80058,cl_80061,cl_80062,cl_80063,cl_80064,cl_80065,cl_80067,cl_80070,cl_80071,cl_80072,cl_80074,cl_80075,cl_80076,cl_80077,cl_80078,cl_80080,cl_80083,cl_80088,cl_80089,cl_80090,cl_80091,cl_80092,cl_80093,cl_80094,cl_80095,cl_80097,cl_80098,cl_80099,cl_80100,cl_80101,cl_80102,cl_80103,cl_80106,cl_80108,cl_80109,cl_80114,cl_80115,cl_80118,cl_80119,cl_80120,cl_80122,cl_80123,cl_80124,cl_80127,cl_80128,cl_80129,cl_80130,cl_80133,cl_80134,cl_80135,cl_80136]
theorem chunk_sound078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk078, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_79476 v h) (hints_cons _ _ _ (der_79477 v h) (hints_cons _ _ _ (der_79478 v h) (hints_cons _ _ _ (der_79480 v h) (hints_cons _ _ _ (der_79481 v h) (hints_cons _ _ _ (der_79482 v h) (hints_cons _ _ _ (der_79484 v h) (hints_cons _ _ _ (der_79485 v h) (hints_cons _ _ _ (der_79486 v h) (hints_cons _ _ _ (der_79487 v h) (hints_cons _ _ _ (der_79489 v h) (hints_cons _ _ _ (der_79491 v h) (hints_cons _ _ _ (der_79492 v h) (hints_cons _ _ _ (der_79493 v h) (hints_cons _ _ _ (der_79494 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_79496 v h) (hints_cons _ _ _ (der_79497 v h) (hints_cons _ _ _ (der_79498 v h) (hints_cons _ _ _ (der_79499 v h) (hints_cons _ _ _ (der_79500 v h) (hints_cons _ _ _ (der_79501 v h) (hints_cons _ _ _ (der_79502 v h) (hints_cons _ _ _ (der_79503 v h) (hints_cons _ _ _ (der_79504 v h) (hints_cons _ _ _ (der_79505 v h) (hints_cons _ _ _ (der_79506 v h) (hints_cons _ _ _ (der_79507 v h) (hints_cons _ _ _ (der_79508 v h) (hints_cons _ _ _ (der_79509 v h) (hints_cons _ _ _ (der_79510 v h) (hints_cons _ _ _ (der_79511 v h) (hints_cons _ _ _ (der_79512 v h) (hints_cons _ _ _ (der_79513 v h) (hints_cons _ _ _ (der_79514 v h) (hints_cons _ _ _ (der_79515 v h) (hints_cons _ _ _ (der_79516 v h) (hints_cons _ _ _ (der_79517 v h) (hints_cons _ _ _ (der_79518 v h) (hints_cons _ _ _ (der_79519 v h) (hints_cons _ _ _ (der_79520 v h) (hints_cons _ _ _ (der_79521 v h) (hints_cons _ _ _ (der_79522 v h) (hints_cons _ _ _ (der_79523 v h) (hints_cons _ _ _ (der_79524 v h) (hints_cons _ _ _ (der_79525 v h) (hints_cons _ _ _ (der_79526 v h) (hints_cons _ _ _ (der_79527 v h) (hints_cons _ _ _ (der_79528 v h) (hints_cons _ _ _ (der_79529 v h) (hints_cons _ _ _ (der_79530 v h) (hints_cons _ _ _ (der_79531 v h) (hints_cons _ _ _ (der_79532 v h) (hints_cons _ _ _ (der_79533 v h) (hints_cons _ _ _ (der_79534 v h) (hints_cons _ _ _ (der_79535 v h) (hints_cons _ _ _ (der_79536 v h) (hints_cons _ _ _ (der_79537 v h) (hints_cons _ _ _ (der_79538 v h) (hints_cons _ _ _ (der_79539 v h) (hints_cons _ _ _ (der_79540 v h) (hints_cons _ _ _ (der_79541 v h) (hints_cons _ _ _ (der_79542 v h) (hints_cons _ _ _ (der_79543 v h) (hints_cons _ _ _ (der_79544 v h) (hints_cons _ _ _ (der_79545 v h) (hints_cons _ _ _ (der_79546 v h) (hints_cons _ _ _ (der_79547 v h) (hints_cons _ _ _ (der_79548 v h) (hints_cons _ _ _ (der_79549 v h) (hints_cons _ _ _ (der_79550 v h) (hints_cons _ _ _ (der_79551 v h) (hints_cons _ _ _ (der_79552 v h) (hints_cons _ _ _ (der_79553 v h) (hints_cons _ _ _ (der_79554 v h) (hints_cons _ _ _ (der_79555 v h) (hints_cons _ _ _ (der_79556 v h) (hints_cons _ _ _ (der_79557 v h) (hints_cons _ _ _ (der_79558 v h) (hints_cons _ _ _ (der_79559 v h) (hints_cons _ _ _ (der_79560 v h) (hints_cons _ _ _ (der_79561 v h) (hints_cons _ _ _ (der_79562 v h) (hints_cons _ _ _ (der_79563 v h) (hints_cons _ _ _ (der_79564 v h) (hints_cons _ _ _ (der_79565 v h) (hints_cons _ _ _ (der_79566 v h) (hints_cons _ _ _ (der_79567 v h) (hints_cons _ _ _ (der_79568 v h) (hints_cons _ _ _ (der_79569 v h) (hints_cons _ _ _ (der_79570 v h) (hints_cons _ _ _ (der_79571 v h) (hints_cons _ _ _ (der_79572 v h) (hints_cons _ _ _ (der_79573 v h) (hints_cons _ _ _ (der_79574 v h) (hints_cons _ _ _ (der_79575 v h) (hints_cons _ _ _ (der_79576 v h) (hints_cons _ _ _ (der_79577 v h) (hints_cons _ _ _ (der_79578 v h) (hints_cons _ _ _ (der_79579 v h) (hints_cons _ _ _ (der_79581 v h) (hints_cons _ _ _ (der_79582 v h) (hints_cons _ _ _ (der_79583 v h) (hints_cons _ _ _ (der_79584 v h) (hints_cons _ _ _ (der_79585 v h) (hints_cons _ _ _ (der_79586 v h) (hints_cons _ _ _ (der_79588 v h) (hints_cons _ _ _ (der_79589 v h) (hints_cons _ _ _ (der_79591 v h) (hints_cons _ _ _ (der_79592 v h) (hints_cons _ _ _ (der_79593 v h) (hints_cons _ _ _ (der_79594 v h) (hints_cons _ _ _ (der_79595 v h) (hints_cons _ _ _ (der_79596 v h) (hints_cons _ _ _ (der_79597 v h) (hints_cons _ _ _ (der_79599 v h) (hints_cons _ _ _ (der_79600 v h) (hints_cons _ _ _ (der_79602 v h) (hints_cons _ _ _ (der_79609 v h) (hints_cons _ _ _ (der_79616 v h) (hints_cons _ _ _ (der_79617 v h) (hints_cons _ _ _ (der_79618 v h) (hints_cons _ _ _ (der_79619 v h) (hints_cons _ _ _ (der_79620 v h) (hints_cons _ _ _ (der_79621 v h) (hints_cons _ _ _ (der_79622 v h) (hints_cons _ _ _ (der_79623 v h) (hints_cons _ _ _ (der_79624 v h) (hints_cons _ _ _ (der_79625 v h) (hints_cons _ _ _ (der_79626 v h) (hints_cons _ _ _ (der_79627 v h) (hints_cons _ _ _ (der_79628 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_79630 v h) (hints_cons _ _ _ (der_79631 v h) (hints_cons _ _ _ (der_79632 v h) (hints_cons _ _ _ (der_79633 v h) (hints_cons _ _ _ (der_79634 v h) (hints_cons _ _ _ (der_79635 v h) (hints_cons _ _ _ (der_79636 v h) (hints_cons _ _ _ (der_79637 v h) (hints_cons _ _ _ (der_79638 v h) (hints_cons _ _ _ (der_79639 v h) (hints_cons _ _ _ (der_79640 v h) (hints_cons _ _ _ (der_79641 v h) (hints_cons _ _ _ (der_79642 v h) (hints_cons _ _ _ (der_79643 v h) (hints_cons _ _ _ (der_79644 v h) (hints_cons _ _ _ (der_79645 v h) (hints_cons _ _ _ (der_79646 v h) (hints_cons _ _ _ (der_79647 v h) (hints_cons _ _ _ (der_79648 v h) (hints_cons _ _ _ (der_79649 v h) (hints_cons _ _ _ (der_79650 v h) (hints_cons _ _ _ (der_79651 v h) (hints_cons _ _ _ (der_79652 v h) (hints_cons _ _ _ (der_79653 v h) (hints_cons _ _ _ (der_79654 v h) (hints_cons _ _ _ (der_79655 v h) (hints_cons _ _ _ (der_79656 v h) (hints_cons _ _ _ (der_79657 v h) (hints_cons _ _ _ (der_79658 v h) (hints_cons _ _ _ (der_79659 v h) (hints_cons _ _ _ (der_79660 v h) (hints_cons _ _ _ (der_79661 v h) (hints_cons _ _ _ (der_79662 v h) (hints_cons _ _ _ (der_79663 v h) (hints_cons _ _ _ (der_79664 v h) (hints_cons _ _ _ (der_79665 v h) (hints_cons _ _ _ (der_79666 v h) (hints_cons _ _ _ (der_79667 v h) (hints_cons _ _ _ (der_79668 v h) (hints_cons _ _ _ (der_79669 v h) (hints_cons _ _ _ (der_79670 v h) (hints_cons _ _ _ (der_79671 v h) (hints_cons _ _ _ (der_79672 v h) (hints_cons _ _ _ (der_79673 v h) (hints_cons _ _ _ (der_79674 v h) (hints_cons _ _ _ (der_79675 v h) (hints_cons _ _ _ (der_79676 v h) (hints_cons _ _ _ (der_79677 v h) (hints_cons _ _ _ (der_79678 v h) (hints_cons _ _ _ (der_79679 v h) (hints_cons _ _ _ (der_79680 v h) (hints_cons _ _ _ (der_79681 v h) (hints_cons _ _ _ (der_79682 v h) (hints_cons _ _ _ (der_79684 v h) (hints_cons _ _ _ (der_79685 v h) (hints_cons _ _ _ (der_79686 v h) (hints_cons _ _ _ (der_79687 v h) (hints_cons _ _ _ (der_79688 v h) (hints_cons _ _ _ (der_79689 v h) (hints_cons _ _ _ (der_79690 v h) (hints_cons _ _ _ (der_79692 v h) (hints_cons _ _ _ (der_79693 v h) (hints_cons _ _ _ (der_79695 v h) (hints_cons _ _ _ (der_79696 v h) (hints_cons _ _ _ (der_79697 v h) (hints_cons _ _ _ (der_79699 v h) (hints_cons _ _ _ (der_79701 v h) (hints_cons _ _ _ (der_79702 v h) (hints_cons _ _ _ (der_79703 v h) (hints_cons _ _ _ (der_79704 v h) (hints_cons _ _ _ (der_79705 v h) (hints_cons _ _ _ (der_79709 v h) (hints_cons _ _ _ (der_79710 v h) (hints_cons _ _ _ (der_79713 v h) (hints_cons _ _ _ (der_79715 v h) (hints_cons _ _ _ (der_79716 v h) (hints_cons _ _ _ (der_79717 v h) (hints_cons _ _ _ (der_79718 v h) (hints_cons _ _ _ (der_79719 v h) (hints_cons _ _ _ (der_79721 v h) (hints_cons _ _ _ (der_79722 v h) (hints_cons _ _ _ (der_79724 v h) (hints_cons _ _ _ (der_79725 v h) (hints_cons _ _ _ (der_79726 v h) (hints_cons _ _ _ (der_79727 v h) (hints_cons _ _ _ (der_79729 v h) (hints_cons _ _ _ (der_79730 v h) (hints_cons _ _ _ (der_79731 v h) (hints_cons _ _ _ (der_79734 v h) (hints_cons _ _ _ (der_79735 v h) (hints_cons _ _ _ (der_79736 v h) (hints_cons _ _ _ (der_79737 v h) (hints_cons _ _ _ (der_79738 v h) (hints_cons _ _ _ (der_79741 v h) (hints_cons _ _ _ (der_79746 v h) (hints_cons _ _ _ (der_79747 v h) (hints_cons _ _ _ (der_79749 v h) (hints_cons _ _ _ (der_79752 v h) (hints_cons _ _ _ (der_79753 v h) (hints_cons _ _ _ (der_79754 v h) (hints_cons _ _ _ (der_79755 v h) (hints_cons _ _ _ (der_79756 v h) (hints_cons _ _ _ (der_79759 v h) (hints_cons _ _ _ (der_79760 v h) (hints_cons _ _ _ (der_79761 v h) (hints_cons _ _ _ (der_79762 v h) (hints_cons _ _ _ (der_79763 v h) (hints_cons _ _ _ (der_79764 v h) (hints_cons _ _ _ (der_79765 v h) (hints_cons _ _ _ (der_79766 v h) (hints_cons _ _ _ (der_79767 v h) (hints_cons _ _ _ (der_79768 v h) (hints_cons _ _ _ (der_79770 v h) (hints_cons _ _ _ (der_79772 v h) (hints_cons _ _ _ (der_79773 v h) (hints_cons _ _ _ (der_79774 v h) (hints_cons _ _ _ (der_79775 v h) (hints_cons _ _ _ (der_79776 v h) (hints_cons _ _ _ (der_79778 v h) (hints_cons _ _ _ (der_79779 v h) (hints_cons _ _ _ (der_79780 v h) (hints_cons _ _ _ (der_79781 v h) (hints_cons _ _ _ (der_79782 v h) (hints_cons _ _ _ (der_79783 v h) (hints_cons _ _ _ (der_79784 v h) (hints_cons _ _ _ (der_79787 v h) (hints_cons _ _ _ (der_79788 v h) (hints_cons _ _ _ (der_79790 v h) (hints_cons _ _ _ (der_79791 v h) (hints_cons _ _ _ (der_79792 v h) (hints_cons _ _ _ (der_79793 v h) (hints_cons _ _ _ (der_79794 v h) (hints_cons _ _ _ (der_79795 v h) (hints_cons _ _ _ (der_79796 v h) (hints_cons _ _ _ (der_79797 v h) (hints_cons _ _ _ (der_79798 v h) (hints_cons _ _ _ (der_79799 v h) (hints_cons _ _ _ (der_79800 v h) (hints_cons _ _ _ (der_79801 v h) (hints_cons _ _ _ (der_79802 v h) (hints_cons _ _ _ (der_79803 v h) (hints_cons _ _ _ (der_79804 v h) (hints_cons _ _ _ (der_79805 v h) (hints_cons _ _ _ (der_79806 v h) (hints_cons _ _ _ (der_79807 v h) (hints_cons _ _ _ (der_79808 v h) (hints_cons _ _ _ (der_79809 v h) (hints_cons _ _ _ (der_79810 v h) (hints_cons _ _ _ (der_79811 v h) (hints_cons _ _ _ (der_79813 v h) (hints_cons _ _ _ (der_79814 v h) (hints_cons _ _ _ (der_79817 v h) (hints_cons _ _ _ (der_79818 v h) (hints_cons _ _ _ (der_79819 v h) (hints_cons _ _ _ (der_79820 v h) (hints_cons _ _ _ (der_79822 v h) (hints_cons _ _ _ (der_79823 v h) (hints_cons _ _ _ (der_79824 v h) (hints_cons _ _ _ (der_79825 v h) (hints_cons _ _ _ (der_79826 v h) (hints_cons _ _ _ (der_79828 v h) (hints_cons _ _ _ (der_79831 v h) (hints_cons _ _ _ (der_79832 v h) (hints_cons _ _ _ (der_79833 v h) (hints_cons _ _ _ (der_79834 v h) (hints_cons _ _ _ (der_79836 v h) (hints_cons _ _ _ (der_79837 v h) (hints_cons _ _ _ (der_79840 v h) (hints_cons _ _ _ (der_79842 v h) (hints_cons _ _ _ (der_79843 v h) (hints_cons _ _ _ (der_79844 v h) (hints_cons _ _ _ (der_79845 v h) (hints_cons _ _ _ (der_79846 v h) (hints_cons _ _ _ (der_79847 v h) (hints_cons _ _ _ (der_79848 v h) (hints_cons _ _ _ (der_79851 v h) (hints_cons _ _ _ (der_79852 v h) (hints_cons _ _ _ (der_79853 v h) (hints_cons _ _ _ (der_79854 v h) (hints_cons _ _ _ (der_79855 v h) (hints_cons _ _ _ (der_79857 v h) (hints_cons _ _ _ (der_79858 v h) (hints_cons _ _ _ (der_79860 v h) (hints_cons _ _ _ (der_79862 v h) (hints_cons _ _ _ (der_79863 v h) (hints_cons _ _ _ (der_79864 v h) (hints_cons _ _ _ (der_79865 v h) (hints_cons _ _ _ (der_79866 v h) (hints_cons _ _ _ (der_79867 v h) (hints_cons _ _ _ (der_79868 v h) (hints_cons _ _ _ (der_79869 v h) (hints_cons _ _ _ (der_79871 v h) (hints_cons _ _ _ (der_79873 v h) (hints_cons _ _ _ (der_79875 v h) (hints_cons _ _ _ (der_79876 v h) (hints_cons _ _ _ (der_79877 v h) (hints_cons _ _ _ (der_79881 v h) (hints_cons _ _ _ (der_79882 v h) (hints_cons _ _ _ (der_79883 v h) (hints_cons _ _ _ (der_79884 v h) (hints_cons _ _ _ (der_79885 v h) (hints_cons _ _ _ (der_79886 v h) (hints_cons _ _ _ (der_79887 v h) (hints_cons _ _ _ (der_79888 v h) (hints_cons _ _ _ (der_79889 v h) (hints_cons _ _ _ (der_79890 v h) (hints_cons _ _ _ (der_79892 v h) (hints_cons _ _ _ (der_79893 v h) (hints_cons _ _ _ (der_79894 v h) (hints_cons _ _ _ (der_79895 v h) (hints_cons _ _ _ (der_79896 v h) (hints_cons _ _ _ (der_79897 v h) (hints_cons _ _ _ (der_79898 v h) (hints_cons _ _ _ (der_79899 v h) (hints_cons _ _ _ (der_79900 v h) (hints_cons _ _ _ (der_79902 v h) (hints_cons _ _ _ (der_79905 v h) (hints_cons _ _ _ (der_79913 v h) (hints_cons _ _ _ (der_79914 v h) (hints_cons _ _ _ (der_79916 v h) (hints_cons _ _ _ (der_79918 v h) (hints_cons _ _ _ (der_79920 v h) (hints_cons _ _ _ (der_79927 v h) (hints_cons _ _ _ (der_79928 v h) (hints_cons _ _ _ (der_79930 v h) (hints_cons _ _ _ (der_79931 v h) (hints_cons _ _ _ (der_79935 v h) (hints_cons _ _ _ (der_79936 v h) (hints_cons _ _ _ (der_79937 v h) (hints_cons _ _ _ (der_79940 v h) (hints_cons _ _ _ (der_79942 v h) (hints_cons _ _ _ (der_79944 v h) (hints_cons _ _ _ (der_79945 v h) (hints_cons _ _ _ (der_79949 v h) (hints_cons _ _ _ (der_79951 v h) (hints_cons _ _ _ (der_79952 v h) (hints_cons _ _ _ (der_79953 v h) (hints_cons _ _ _ (der_79954 v h) (hints_cons _ _ _ (der_79955 v h) (hints_cons _ _ _ (der_79957 v h) (hints_cons _ _ _ (der_79958 v h) (hints_cons _ _ _ (der_79960 v h) (hints_cons _ _ _ (der_79961 v h) (hints_cons _ _ _ (der_79963 v h) (hints_cons _ _ _ (der_79964 v h) (hints_cons _ _ _ (der_79966 v h) (hints_cons _ _ _ (der_79968 v h) (hints_cons _ _ _ (der_79969 v h) (hints_cons _ _ _ (der_79970 v h) (hints_cons _ _ _ (der_79971 v h) (hints_cons _ _ _ (der_79972 v h) (hints_cons _ _ _ (der_79973 v h) (hints_cons _ _ _ (der_79974 v h) (hints_cons _ _ _ (der_79976 v h) (hints_cons _ _ _ (der_79977 v h) (hints_cons _ _ _ (der_79978 v h) (hints_cons _ _ _ (der_79979 v h) (hints_cons _ _ _ (der_79980 v h) (hints_cons _ _ _ (der_79982 v h) (hints_cons _ _ _ (der_79983 v h) (hints_cons _ _ _ (der_79984 v h) (hints_cons _ _ _ (der_79986 v h) (hints_cons _ _ _ (der_79987 v h) (hints_cons _ _ _ (der_79988 v h) (hints_cons _ _ _ (der_79989 v h) (hints_cons _ _ _ (der_79990 v h) (hints_cons _ _ _ (der_79992 v h) (hints_cons _ _ _ (der_79993 v h) (hints_cons _ _ _ (der_79994 v h) (hints_cons _ _ _ (der_79996 v h) (hints_cons _ _ _ (der_79997 v h) (hints_cons _ _ _ (der_79998 v h) (hints_cons _ _ _ (der_79999 v h) (hints_cons _ _ _ (der_80000 v h) (hints_cons _ _ _ (der_80002 v h) (hints_cons _ _ _ (der_80003 v h) (hints_cons _ _ _ (der_80004 v h) (hints_cons _ _ _ (der_80005 v h) (hints_cons _ _ _ (der_80007 v h) (hints_cons _ _ _ (der_80008 v h) (hints_cons _ _ _ (der_80009 v h) (hints_cons _ _ _ (der_80010 v h) (hints_cons _ _ _ (der_80012 v h) (hints_cons _ _ _ (der_80013 v h) (hints_cons _ _ _ (der_80015 v h) (hints_cons _ _ _ (der_80018 v h) (hints_cons _ _ _ (der_80019 v h) (hints_cons _ _ _ (der_80020 v h) (hints_cons _ _ _ (der_80021 v h) (hints_cons _ _ _ (der_80022 v h) (hints_cons _ _ _ (der_80023 v h) (hints_cons _ _ _ (der_80024 v h) (hints_cons _ _ _ (der_80027 v h) (hints_cons _ _ _ (der_80029 v h) (hints_cons _ _ _ (der_80030 v h) (hints_cons _ _ _ (der_80033 v h) (hints_cons _ _ _ (der_80034 v h) (hints_cons _ _ _ (der_80035 v h) (hints_cons _ _ _ (der_80036 v h) (hints_cons _ _ _ (der_80037 v h) (hints_cons _ _ _ (der_80038 v h) (hints_cons _ _ _ (der_80039 v h) (hints_cons _ _ _ (der_80040 v h) (hints_cons _ _ _ (der_80042 v h) (hints_cons _ _ _ (der_80043 v h) (hints_cons _ _ _ (der_80044 v h) (hints_cons _ _ _ (der_80045 v h) (hints_cons _ _ _ (der_80046 v h) (hints_cons _ _ _ (der_80048 v h) (hints_cons _ _ _ (der_80049 v h) (hints_cons _ _ _ (der_80050 v h) (hints_cons _ _ _ (der_80051 v h) (hints_cons _ _ _ (der_80052 v h) (hints_cons _ _ _ (der_80054 v h) (hints_cons _ _ _ (der_80055 v h) (hints_cons _ _ _ (der_80057 v h) (hints_cons _ _ _ (der_80058 v h) (hints_cons _ _ _ (der_80061 v h) (hints_cons _ _ _ (der_80062 v h) (hints_cons _ _ _ (der_80063 v h) (hints_cons _ _ _ (der_80064 v h) (hints_cons _ _ _ (der_80065 v h) (hints_cons _ _ _ (der_80067 v h) (hints_cons _ _ _ (der_80070 v h) (hints_cons _ _ _ (der_80071 v h) (hints_cons _ _ _ (der_80072 v h) (hints_cons _ _ _ (der_80074 v h) (hints_cons _ _ _ (der_80075 v h) (hints_cons _ _ _ (der_80076 v h) (hints_cons _ _ _ (der_80077 v h) (hints_cons _ _ _ (der_80078 v h) (hints_cons _ _ _ (der_80080 v h) (hints_cons _ _ _ (der_80083 v h) (hints_cons _ _ _ (der_80088 v h) (hints_cons _ _ _ (der_80089 v h) (hints_cons _ _ _ (der_80090 v h) (hints_cons _ _ _ (der_80091 v h) (hints_cons _ _ _ (der_80092 v h) (hints_cons _ _ _ (der_80093 v h) (hints_cons _ _ _ (der_80094 v h) (hints_cons _ _ _ (der_80095 v h) (hints_cons _ _ _ (der_80097 v h) (hints_cons _ _ _ (der_80098 v h) (hints_cons _ _ _ (der_80099 v h) (hints_cons _ _ _ (der_80100 v h) (hints_cons _ _ _ (der_80101 v h) (hints_cons _ _ _ (der_80102 v h) (hints_cons _ _ _ (der_80103 v h) (hints_cons _ _ _ (der_80106 v h) (hints_cons _ _ _ (der_80108 v h) (hints_cons _ _ _ (der_80109 v h) (hints_cons _ _ _ (der_80114 v h) (hints_cons _ _ _ (der_80115 v h) (hints_cons _ _ _ (der_80118 v h) (hints_cons _ _ _ (der_80119 v h) (hints_cons _ _ _ (der_80120 v h) (hints_cons _ _ _ (der_80122 v h) (hints_cons _ _ _ (der_80123 v h) (hints_cons _ _ _ (der_80124 v h) (hints_cons _ _ _ (der_80127 v h) (hints_cons _ _ _ (der_80128 v h) (hints_cons _ _ _ (der_80129 v h) (hints_cons _ _ _ (der_80130 v h) (hints_cons _ _ _ (der_80133 v h) (hints_cons _ _ _ (der_80134 v h) (hints_cons _ _ _ (der_80135 v h) (hints_cons _ _ _ (der_80136 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix078 := prefix077 ++ chunk078
theorem prefix_sound078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix078, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound077 v h c hc
  · exact chunk_sound078 v h c hc
end Percolation.NReplay
