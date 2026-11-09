import NReplay060
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_62315 : CNF.NClause := [(90,false),(151,false),(69,false),(80,false),(70,false),(135,true),(130,true),(17,true),(65,false),(142,false),(125,true),(21,true),(901,true),(139,true),(132,true),(126,true),(26,true),(140,true),(148,true),(144,true),(146,true),(67,true),(138,true)]
theorem der_62315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62315 :=
  CNF.rup_sound cl_62315 [cl_15791,cl_15783,cl_8052,cl_56345,cl_15784,cl_61974,cl_62283,cl_62308,cl_8099,cl_15771,cl_49789,cl_15652,cl_62314,cl_62307,cl_62078,cl_62077,cl_15887,cl_62068,cl_49757,cl_52703,cl_62313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (inp_8052 v h) (hints_cons _ _ _ (der_56345 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_61974 v h) (hints_cons _ _ _ (der_62283 v h) (hints_cons _ _ _ (der_62308 v h) (hints_cons _ _ _ (inp_8099 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_49789 v h) (hints_cons _ _ _ (der_15652 v h) (hints_cons _ _ _ (der_62314 v h) (hints_cons _ _ _ (der_62307 v h) (hints_cons _ _ _ (der_62078 v h) (hints_cons _ _ _ (der_62077 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_62068 v h) (hints_cons _ _ _ (der_49757 v h) (hints_cons _ _ _ (der_52703 v h) (hints_cons _ _ _ (der_62313 v h) (by intro d hd; cases hd))))))))))))))))))))))
def cl_62316 : CNF.NClause := [(151,false),(69,false),(80,false),(70,false),(135,true),(52,true),(130,true),(17,true),(65,false),(142,false),(125,true),(21,true),(901,true),(139,true),(132,true),(126,true),(26,true),(140,true),(148,true),(144,true),(146,true),(67,true),(138,true)]
theorem der_62316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62316 :=
  CNF.rup_sound cl_62316 [cl_15784,cl_15783,cl_61974,cl_15791,cl_62283,cl_62308,cl_8099,cl_15771,cl_49789,cl_15770,cl_61675,cl_49990,cl_61924,cl_15652,cl_62314,cl_62307,cl_57470,cl_15785,cl_15792,cl_8052,cl_57527,cl_15776,cl_56345,cl_58950,cl_37437,cl_5249,cl_62315,cl_58202,cl_62159,cl_15793,cl_52368,cl_8021,cl_15619,cl_8104,cl_8076,cl_8049,cl_15794,cl_15779,cl_15773,cl_62018,cl_15629,cl_15775,cl_62169,cl_50082,cl_49946,cl_61678,cl_15778,cl_62139,cl_5121,cl_57604,cl_61361,cl_38351,cl_49886,cl_59920,cl_5505,cl_36075,cl_62276,cl_49849,cl_59723,cl_50288,cl_54984,cl_7966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_61974 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_62283 v h) (hints_cons _ _ _ (der_62308 v h) (hints_cons _ _ _ (inp_8099 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_49789 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_61675 v h) (hints_cons _ _ _ (der_49990 v h) (hints_cons _ _ _ (der_61924 v h) (hints_cons _ _ _ (der_15652 v h) (hints_cons _ _ _ (der_62314 v h) (hints_cons _ _ _ (der_62307 v h) (hints_cons _ _ _ (der_57470 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (inp_8052 v h) (hints_cons _ _ _ (der_57527 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (der_56345 v h) (hints_cons _ _ _ (der_58950 v h) (hints_cons _ _ _ (der_37437 v h) (hints_cons _ _ _ (inp_5249 v h) (hints_cons _ _ _ (der_62315 v h) (hints_cons _ _ _ (der_58202 v h) (hints_cons _ _ _ (der_62159 v h) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_52368 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_15619 v h) (hints_cons _ _ _ (inp_8104 v h) (hints_cons _ _ _ (inp_8076 v h) (hints_cons _ _ _ (inp_8049 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_62018 v h) (hints_cons _ _ _ (der_15629 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_62169 v h) (hints_cons _ _ _ (der_50082 v h) (hints_cons _ _ _ (der_49946 v h) (hints_cons _ _ _ (der_61678 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_62139 v h) (hints_cons _ _ _ (inp_5121 v h) (hints_cons _ _ _ (der_57604 v h) (hints_cons _ _ _ (der_61361 v h) (hints_cons _ _ _ (der_38351 v h) (hints_cons _ _ _ (der_49886 v h) (hints_cons _ _ _ (der_59920 v h) (hints_cons _ _ _ (inp_5505 v h) (hints_cons _ _ _ (der_36075 v h) (hints_cons _ _ _ (der_62276 v h) (hints_cons _ _ _ (der_49849 v h) (hints_cons _ _ _ (der_59723 v h) (hints_cons _ _ _ (der_50288 v h) (hints_cons _ _ _ (der_54984 v h) (hints_cons _ _ _ (inp_7966 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_62317 : CNF.NClause := [(69,false),(80,false),(70,false),(135,true),(52,true),(130,true),(17,true),(65,false),(142,false),(125,true),(21,true),(901,true),(139,true),(132,true),(126,true),(26,true),(140,true),(148,true),(144,true),(146,true),(67,true),(138,true)]
theorem der_62317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62317 :=
  CNF.rup_sound cl_62317 [cl_61974,cl_15783,cl_15652,cl_62314,cl_15791,cl_62307,cl_57470,cl_15785,cl_58082,cl_62283,cl_15784,cl_62308,cl_15770,cl_61924,cl_8099,cl_49990,cl_15771,cl_62301,cl_49789,cl_62316,cl_15663,cl_8069,cl_8055,cl_8012,cl_15773,cl_62018,cl_15629,cl_15779,cl_58060,cl_8042,cl_15775,cl_60497,cl_62169,cl_8050,cl_49946,cl_15778,cl_62139,cl_35284,cl_15617,cl_15769,cl_49886,cl_59920,cl_5505,cl_5121,cl_62096,cl_56674,cl_15793,cl_42525,cl_49682,cl_59167,cl_52287,cl_58202,cl_7553,cl_53803,cl_4353,cl_57876,cl_54282,cl_53632,cl_61940,cl_49730,cl_7965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61974 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15652 v h) (hints_cons _ _ _ (der_62314 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_62307 v h) (hints_cons _ _ _ (der_57470 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_58082 v h) (hints_cons _ _ _ (der_62283 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_62308 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_61924 v h) (hints_cons _ _ _ (inp_8099 v h) (hints_cons _ _ _ (der_49990 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_62301 v h) (hints_cons _ _ _ (der_49789 v h) (hints_cons _ _ _ (der_62316 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (inp_8069 v h) (hints_cons _ _ _ (inp_8055 v h) (hints_cons _ _ _ (inp_8012 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_62018 v h) (hints_cons _ _ _ (der_15629 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_58060 v h) (hints_cons _ _ _ (inp_8042 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_60497 v h) (hints_cons _ _ _ (der_62169 v h) (hints_cons _ _ _ (inp_8050 v h) (hints_cons _ _ _ (der_49946 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_62139 v h) (hints_cons _ _ _ (der_35284 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_49886 v h) (hints_cons _ _ _ (der_59920 v h) (hints_cons _ _ _ (inp_5505 v h) (hints_cons _ _ _ (inp_5121 v h) (hints_cons _ _ _ (der_62096 v h) (hints_cons _ _ _ (der_56674 v h) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_42525 v h) (hints_cons _ _ _ (der_49682 v h) (hints_cons _ _ _ (der_59167 v h) (hints_cons _ _ _ (der_52287 v h) (hints_cons _ _ _ (der_58202 v h) (hints_cons _ _ _ (inp_7553 v h) (hints_cons _ _ _ (der_53803 v h) (hints_cons _ _ _ (inp_4353 v h) (hints_cons _ _ _ (der_57876 v h) (hints_cons _ _ _ (der_54282 v h) (hints_cons _ _ _ (der_53632 v h) (hints_cons _ _ _ (der_61940 v h) (hints_cons _ _ _ (der_49730 v h) (hints_cons _ _ _ (inp_7965 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_62318 : CNF.NClause := [(69,true),(142,false),(79,true)]
theorem der_62318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62318 :=
  CNF.rup_sound cl_62318 [cl_15784,cl_57911,cl_62290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_57911 v h) (hints_cons _ _ _ (der_62290 v h) (by intro d hd; cases hd))))
def cl_62319 : CNF.NClause := [(11,false),(80,true),(141,true),(125,true),(132,true),(126,true),(140,true),(144,true),(146,true)]
theorem der_62319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62319 :=
  CNF.rup_sound cl_62319 [cl_62000,cl_42483,cl_15794,cl_37515,cl_15769,cl_15773,cl_15661,cl_15628,cl_8009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62000 v h) (hints_cons _ _ _ (der_42483 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_37515 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15628 v h) (hints_cons _ _ _ (inp_8009 v h) (by intro d hd; cases hd))))))))))
def cl_62321 : CNF.NClause := [(153,false),(11,true),(80,true)]
theorem der_62321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62321 :=
  CNF.rup_sound cl_62321 [cl_15794,cl_58004,cl_61609,cl_30462,cl_60466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_58004 v h) (hints_cons _ _ _ (der_61609 v h) (hints_cons _ _ _ (der_30462 v h) (hints_cons _ _ _ (der_60466 v h) (by intro d hd; cases hd))))))
def cl_62322 : CNF.NClause := [(80,true),(135,true),(130,true),(143,false),(141,true),(142,false),(125,true),(132,true),(126,true),(150,true),(140,true),(148,true),(144,true),(147,true),(146,true),(138,true)]
theorem der_62322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62322 :=
  CNF.rup_sound cl_62322 [cl_62319,cl_62321,cl_8114,cl_8042,cl_8098,cl_8055,cl_8009,cl_15619,cl_15628,cl_8016,cl_15773,cl_15769,cl_60466,cl_60635,cl_30435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62319 v h) (hints_cons _ _ _ (der_62321 v h) (hints_cons _ _ _ (inp_8114 v h) (hints_cons _ _ _ (inp_8042 v h) (hints_cons _ _ _ (inp_8098 v h) (hints_cons _ _ _ (inp_8055 v h) (hints_cons _ _ _ (inp_8009 v h) (hints_cons _ _ _ (der_15619 v h) (hints_cons _ _ _ (der_15628 v h) (hints_cons _ _ _ (inp_8016 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_60466 v h) (hints_cons _ _ _ (der_60635 v h) (hints_cons _ _ _ (der_30435 v h) (by intro d hd; cases hd))))))))))))))))
def cl_62323 : CNF.NClause := [(131,false),(54,true),(137,false),(152,true),(127,true),(80,false),(78,false),(135,true),(17,true),(69,false),(65,false),(142,false),(125,true),(21,true),(139,true),(126,true),(26,true),(140,true),(148,true),(144,true),(147,true),(146,true)]
theorem der_62323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62323 :=
  CNF.rup_sound cl_62323 [cl_15784,cl_8103,cl_15771,cl_49789,cl_15661,cl_15770,cl_49990,cl_61924,cl_15779,cl_15783,cl_15652,cl_62314,cl_57470,cl_62283,cl_15791,cl_15773,cl_62018,cl_15629,cl_8080,cl_49946,cl_15778,cl_58644,cl_61053,cl_62139,cl_8085,cl_15794,cl_15617,cl_49886,cl_59920,cl_5505,cl_15775,cl_60497,cl_8050,cl_50082,cl_15792,cl_57527,cl_49682,cl_15776,cl_5121,cl_57604,cl_62096,cl_61678,cl_37437,cl_49932,cl_61361,cl_38351,cl_5249,cl_50814,cl_49847,cl_54984,cl_43800,cl_49957,cl_7964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (inp_8103 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_49789 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_49990 v h) (hints_cons _ _ _ (der_61924 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15652 v h) (hints_cons _ _ _ (der_62314 v h) (hints_cons _ _ _ (der_57470 v h) (hints_cons _ _ _ (der_62283 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_62018 v h) (hints_cons _ _ _ (der_15629 v h) (hints_cons _ _ _ (inp_8080 v h) (hints_cons _ _ _ (der_49946 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_58644 v h) (hints_cons _ _ _ (der_61053 v h) (hints_cons _ _ _ (der_62139 v h) (hints_cons _ _ _ (inp_8085 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_49886 v h) (hints_cons _ _ _ (der_59920 v h) (hints_cons _ _ _ (inp_5505 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_60497 v h) (hints_cons _ _ _ (inp_8050 v h) (hints_cons _ _ _ (der_50082 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_57527 v h) (hints_cons _ _ _ (der_49682 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (inp_5121 v h) (hints_cons _ _ _ (der_57604 v h) (hints_cons _ _ _ (der_62096 v h) (hints_cons _ _ _ (der_61678 v h) (hints_cons _ _ _ (der_37437 v h) (hints_cons _ _ _ (der_49932 v h) (hints_cons _ _ _ (der_61361 v h) (hints_cons _ _ _ (der_38351 v h) (hints_cons _ _ _ (inp_5249 v h) (hints_cons _ _ _ (der_50814 v h) (hints_cons _ _ _ (der_49847 v h) (hints_cons _ _ _ (der_54984 v h) (hints_cons _ _ _ (der_43800 v h) (hints_cons _ _ _ (der_49957 v h) (hints_cons _ _ _ (inp_7964 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_62324 : CNF.NClause := [(17,true),(125,true),(26,true),(140,true),(67,true),(79,true)]
theorem der_62324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62324 :=
  CNF.rup_sound cl_62324 [cl_62272,cl_62318,cl_62098,cl_62283,cl_15887,cl_62092,cl_15891,cl_62086,cl_62222,cl_12724,cl_62281,cl_56741,cl_58061,cl_59022,cl_56917,cl_15791,cl_61972,cl_61974,cl_61975,cl_15641,cl_56745,cl_15783,cl_15652,cl_57470,cl_62306,cl_34441,cl_15638,cl_62307,cl_62314,cl_62322,cl_62317,cl_61990,cl_56869,cl_15632,cl_15661,cl_8103,cl_15770,cl_15771,cl_61675,cl_50784,cl_62323,cl_15663,cl_8076,cl_15619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62272 v h) (hints_cons _ _ _ (der_62318 v h) (hints_cons _ _ _ (der_62098 v h) (hints_cons _ _ _ (der_62283 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_62092 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_62086 v h) (hints_cons _ _ _ (der_62222 v h) (hints_cons _ _ _ (inp_12724 v h) (hints_cons _ _ _ (der_62281 v h) (hints_cons _ _ _ (der_56741 v h) (hints_cons _ _ _ (der_58061 v h) (hints_cons _ _ _ (der_59022 v h) (hints_cons _ _ _ (der_56917 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_61972 v h) (hints_cons _ _ _ (der_61974 v h) (hints_cons _ _ _ (der_61975 v h) (hints_cons _ _ _ (der_15641 v h) (hints_cons _ _ _ (der_56745 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15652 v h) (hints_cons _ _ _ (der_57470 v h) (hints_cons _ _ _ (der_62306 v h) (hints_cons _ _ _ (der_34441 v h) (hints_cons _ _ _ (der_15638 v h) (hints_cons _ _ _ (der_62307 v h) (hints_cons _ _ _ (der_62314 v h) (hints_cons _ _ _ (der_62322 v h) (hints_cons _ _ _ (der_62317 v h) (hints_cons _ _ _ (der_61990 v h) (hints_cons _ _ _ (der_56869 v h) (hints_cons _ _ _ (der_15632 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (inp_8103 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_61675 v h) (hints_cons _ _ _ (der_50784 v h) (hints_cons _ _ _ (der_62323 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (inp_8076 v h) (hints_cons _ _ _ (der_15619 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))
def cl_62332 : CNF.NClause := [(83,true),(5,false),(17,false),(26,true)]
theorem der_62332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62332 :=
  CNF.rup_sound cl_62332 [cl_54102,cl_62010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54102 v h) (hints_cons _ _ _ (der_62010 v h) (by intro d hd; cases hd)))
def cl_62333 : CNF.NClause := [(133,false),(40,true),(81,false),(82,false),(75,false),(17,false),(69,false)]
theorem der_62333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62333 :=
  CNF.rup_sound cl_62333 [cl_15775,cl_62149,cl_43285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_62149 v h) (hints_cons _ _ _ (der_43285 v h) (by intro d hd; cases hd))))
def cl_62338 : CNF.NClause := [(80,true),(7,false),(3,false)]
theorem der_62338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62338 :=
  CNF.rup_sound cl_62338 [cl_42483,cl_43611,cl_60635,cl_30435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42483 v h) (hints_cons _ _ _ (der_43611 v h) (hints_cons _ _ _ (der_60635 v h) (hints_cons _ _ _ (der_30435 v h) (by intro d hd; cases hd)))))
def cl_62339 : CNF.NClause := [(136,false),(91,false),(43,true),(72,false),(81,false),(85,false),(64,false),(132,true),(140,true),(144,true)]
theorem der_62339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62339 :=
  CNF.rup_sound cl_62339 [cl_15778,cl_62105,cl_5505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_62105 v h) (hints_cons _ _ _ (inp_5505 v h) (by intro d hd; cases hd))))
def cl_62340 : CNF.NClause := [(133,true),(136,true),(153,true),(135,true),(142,false),(125,true),(139,true),(126,true),(150,true),(144,true),(147,true)]
theorem der_62340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62340 :=
  CNF.rup_sound cl_62340 [cl_8012,cl_8082,cl_15619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8012 v h) (hints_cons _ _ _ (inp_8082 v h) (hints_cons _ _ _ (der_15619 v h) (by intro d hd; cases hd))))
def cl_62349 : CNF.NClause := [(74,true),(41,false),(73,false),(75,false)]
theorem der_62349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62349 :=
  CNF.rup_sound cl_62349 [cl_51250,cl_51252,cl_51234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51250 v h) (hints_cons _ _ _ (der_51252 v h) (hints_cons _ _ _ (der_51234 v h) (by intro d hd; cases hd))))
def cl_62353 : CNF.NClause := [(81,true),(153,true),(135,true),(142,false),(125,true),(139,true),(126,true),(150,true),(144,true),(147,true)]
theorem der_62353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62353 :=
  CNF.rup_sound cl_62353 [cl_61053,cl_62169,cl_62340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61053 v h) (hints_cons _ _ _ (der_62169 v h) (hints_cons _ _ _ (der_62340 v h) (by intro d hd; cases hd))))
def cl_62355 : CNF.NClause := [(74,true),(10,false),(29,false)]
theorem der_62355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62355 :=
  CNF.rup_sound cl_62355 [cl_61744,cl_61614,cl_50104,cl_30543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61744 v h) (hints_cons _ _ _ (der_61614 v h) (hints_cons _ _ _ (der_50104 v h) (hints_cons _ _ _ (der_30543 v h) (by intro d hd; cases hd)))))
def cl_62357 : CNF.NClause := [(83,true),(128,false),(17,false),(26,true)]
theorem der_62357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62357 :=
  CNF.rup_sound cl_62357 [cl_62010,cl_50523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62010 v h) (hints_cons _ _ _ (der_50523 v h) (by intro d hd; cases hd)))
def cl_62365 : CNF.NClause := [(926,false),(85,true),(21,true)]
theorem der_62365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62365 :=
  CNF.rup_sound cl_62365 [cl_15887,cl_15892,cl_50156,cl_53985,cl_15871,cl_54299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_50156 v h) (hints_cons _ _ _ (der_53985 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_54299 v h) (by intro d hd; cases hd)))))))
def cl_62370 : CNF.NClause := [(101,true),(59,false),(48,false)]
theorem der_62370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62370 :=
  CNF.rup_sound cl_62370 [cl_49845,cl_50274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49845 v h) (hints_cons _ _ _ (der_50274 v h) (by intro d hd; cases hd)))
def cl_62389 : CNF.NClause := [(60,true),(74,false),(151,false),(152,true),(3,false),(88,false),(68,false),(86,false),(29,false),(150,true)]
theorem der_62389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62389 :=
  CNF.rup_sound cl_62389 [cl_35755,cl_7681,cl_61804,cl_42483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35755 v h) (hints_cons _ _ _ (inp_7681 v h) (hints_cons _ _ _ (der_61804 v h) (hints_cons _ _ _ (der_42483 v h) (by intro d hd; cases hd)))))
def cl_62391 : CNF.NClause := [(50,false),(116,true),(43,false),(52,true)]
theorem der_62391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62391 :=
  CNF.rup_sound cl_62391 [cl_50503,cl_50294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50503 v h) (hints_cons _ _ _ (der_50294 v h) (by intro d hd; cases hd)))
def cl_62393 : CNF.NClause := [(71,true),(20,false),(144,false)]
theorem der_62393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62393 :=
  CNF.rup_sound cl_62393 [cl_42582,cl_61781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42582 v h) (hints_cons _ _ _ (der_61781 v h) (by intro d hd; cases hd)))
def cl_62396 : CNF.NClause := [(69,true),(11,false),(151,false)]
theorem der_62396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62396 :=
  CNF.rup_sound cl_62396 [cl_39879,cl_61156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39879 v h) (hints_cons _ _ _ (der_61156 v h) (by intro d hd; cases hd)))
def cl_62402 : CNF.NClause := [(80,true),(7,false),(139,false)]
theorem der_62402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62402 :=
  CNF.rup_sound cl_62402 [cl_62338,cl_61655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62338 v h) (hints_cons _ _ _ (der_61655 v h) (by intro d hd; cases hd)))
def cl_62405 : CNF.NClause := [(68,true),(29,false),(140,false)]
theorem der_62405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62405 :=
  CNF.rup_sound cl_62405 [cl_49530,cl_57249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49530 v h) (hints_cons _ _ _ (der_57249 v h) (by intro d hd; cases hd)))
def cl_62409 : CNF.NClause := [(68,true),(12,false),(140,false)]
theorem der_62409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62409 :=
  CNF.rup_sound cl_62409 [cl_49989,cl_57249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49989 v h) (hints_cons _ _ _ (der_57249 v h) (by intro d hd; cases hd)))
def cl_62411 : CNF.NClause := [(86,true),(18,false),(142,false)]
theorem der_62411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62411 :=
  CNF.rup_sound cl_62411 [cl_49789,cl_57992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49789 v h) (hints_cons _ _ _ (der_57992 v h) (by intro d hd; cases hd)))
def cl_62414 : CNF.NClause := [(86,true),(1,false),(125,false)]
theorem der_62414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62414 :=
  CNF.rup_sound cl_62414 [cl_49797,cl_59455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49797 v h) (hints_cons _ _ _ (der_59455 v h) (by intro d hd; cases hd)))
def cl_62416 : CNF.NClause := [(84,true),(2,false),(126,false)]
theorem der_62416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62416 :=
  CNF.rup_sound cl_62416 [cl_37830,cl_58791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37830 v h) (hints_cons _ _ _ (der_58791 v h) (by intro d hd; cases hd)))
def cl_62424 : CNF.NClause := [(85,true),(3,false),(127,false)]
theorem der_62424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62424 :=
  CNF.rup_sound cl_62424 [cl_42433,cl_57862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42433 v h) (hints_cons _ _ _ (der_57862 v h) (by intro d hd; cases hd)))
def cl_62431 : CNF.NClause := [(85,true),(12,false),(136,false)]
theorem der_62431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62431 :=
  CNF.rup_sound cl_62431 [cl_49888,cl_57949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49888 v h) (hints_cons _ _ _ (der_57949 v h) (by intro d hd; cases hd)))
def cl_62447 : CNF.NClause := [(82,true),(9,false),(129,false)]
theorem der_62447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62447 :=
  CNF.rup_sound cl_62447 [cl_49774,cl_54137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49774 v h) (hints_cons _ _ _ (der_54137 v h) (by intro d hd; cases hd)))
def cl_62452 : CNF.NClause := [(80,true),(139,false)]
theorem der_62452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62452 :=
  CNF.rup_sound cl_62452 [cl_62402,cl_61466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62402 v h) (hints_cons _ _ _ (der_61466 v h) (by intro d hd; cases hd)))
def cl_62455 : CNF.NClause := [(82,true),(129,false)]
theorem der_62455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62455 :=
  CNF.rup_sound cl_62455 [cl_62447,cl_45060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62447 v h) (hints_cons _ _ _ (der_45060 v h) (by intro d hd; cases hd)))
def cl_62461 : CNF.NClause := [(80,true),(29,false),(153,false)]
theorem der_62461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62461 :=
  CNF.rup_sound cl_62461 [cl_62000,cl_62321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62000 v h) (hints_cons _ _ _ (der_62321 v h) (by intro d hd; cases hd)))
def cl_62463 : CNF.NClause := [(69,true),(151,false)]
theorem der_62463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62463 :=
  CNF.rup_sound cl_62463 [cl_62396,cl_57258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62396 v h) (hints_cons _ _ _ (der_57258 v h) (by intro d hd; cases hd)))
def cl_62466 : CNF.NClause := [(14,false),(72,true),(138,false)]
theorem der_62466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62466 :=
  CNF.rup_sound cl_62466 [cl_49819,cl_48382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49819 v h) (hints_cons _ _ _ (der_48382 v h) (by intro d hd; cases hd)))
def cl_62474 : CNF.NClause := [(70,true),(3,false),(152,false)]
theorem der_62474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62474 :=
  CNF.rup_sound cl_62474 [cl_54024,cl_56869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54024 v h) (hints_cons _ _ _ (der_56869 v h) (by intro d hd; cases hd)))
def cl_62484 : CNF.NClause := [(70,true),(14,false),(152,false)]
theorem der_62484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62484 :=
  CNF.rup_sound cl_62484 [cl_53670,cl_56869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53670 v h) (hints_cons _ _ _ (der_56869 v h) (by intro d hd; cases hd)))
def cl_62489 : CNF.NClause := [(70,true),(6,false),(130,false)]
theorem der_62489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62489 :=
  CNF.rup_sound cl_62489 [cl_62207,cl_62266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62207 v h) (hints_cons _ _ _ (der_62266 v h) (by intro d hd; cases hd)))
def cl_62507 : CNF.NClause := [(15,false),(79,true),(126,false)]
theorem der_62507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62507 :=
  CNF.rup_sound cl_62507 [cl_49936,cl_56917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49936 v h) (hints_cons _ _ _ (der_56917 v h) (by intro d hd; cases hd)))
def cl_62510 : CNF.NClause := [(61,false),(67,false)]
theorem der_62510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62510 :=
  CNF.rup_sound cl_62510 [cl_57918,cl_49614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57918 v h) (hints_cons _ _ _ (der_49614 v h) (by intro d hd; cases hd)))
def cl_62559 : CNF.NClause := [(61,false)]
theorem der_62559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62559 :=
  CNF.rup_sound cl_62559 [cl_62510,cl_49757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62510 v h) (hints_cons _ _ _ (der_49757 v h) (by intro d hd; cases hd)))
def cl_62560 : CNF.NClause := [(31,false),(88,true)]
theorem der_62560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62560 :=
  CNF.rup_sound cl_62560 [cl_49684,cl_50059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49684 v h) (hints_cons _ _ _ (der_50059 v h) (by intro d hd; cases hd)))
def cl_62561 : CNF.NClause := [(31,false)]
theorem der_62561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62561 :=
  CNF.rup_sound cl_62561 [cl_49681,cl_62560,cl_49682,cl_49683,cl_51572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49681 v h) (hints_cons _ _ _ (der_62560 v h) (hints_cons _ _ _ (der_49682 v h) (hints_cons _ _ _ (der_49683 v h) (hints_cons _ _ _ (der_51572 v h) (by intro d hd; cases hd))))))
def cl_62562 : CNF.NClause := [(153,false),(80,true)]
theorem der_62562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62562 :=
  CNF.rup_sound cl_62562 [cl_15794,cl_62461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_62461 v h) (by intro d hd; cases hd)))
def cl_62563 : CNF.NClause := [(138,false),(72,true)]
theorem der_62563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62563 :=
  CNF.rup_sound cl_62563 [cl_15780,cl_62466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_62466 v h) (by intro d hd; cases hd)))
def cl_62564 : CNF.NClause := [(128,false),(68,true)]
theorem der_62564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62564 :=
  CNF.rup_sound cl_62564 [cl_15770,cl_49990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_49990 v h) (by intro d hd; cases hd)))
def cl_62565 : CNF.NClause := [(128,false),(63,true)]
theorem der_62565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62565 :=
  CNF.rup_sound cl_62565 [cl_15770,cl_61924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_61924 v h) (by intro d hd; cases hd)))
def cl_62566 : CNF.NClause := [(125,false),(86,true)]
theorem der_62566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62566 :=
  CNF.rup_sound cl_62566 [cl_15767,cl_62414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_62414 v h) (by intro d hd; cases hd)))
def cl_62569 : CNF.NClause := [(144,false),(71,true)]
theorem der_62569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62569 :=
  CNF.rup_sound cl_62569 [cl_15786,cl_62393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_62393 v h) (by intro d hd; cases hd)))
def cl_62571 : CNF.NClause := [(136,false),(72,true)]
theorem der_62571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62571 :=
  CNF.rup_sound cl_62571 [cl_15778,cl_58644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_58644 v h) (by intro d hd; cases hd)))
def cl_62572 : CNF.NClause := [(136,false),(85,true)]
theorem der_62572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62572 :=
  CNF.rup_sound cl_62572 [cl_15778,cl_62431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_62431 v h) (by intro d hd; cases hd)))
def cl_62573 : CNF.NClause := [(130,false),(66,true)]
theorem der_62573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62573 :=
  CNF.rup_sound cl_62573 [cl_15772,cl_49986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_49986 v h) (by intro d hd; cases hd)))
def cl_62574 : CNF.NClause := [(130,false),(70,true)]
theorem der_62574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62574 :=
  CNF.rup_sound cl_62574 [cl_15772,cl_62489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_62489 v h) (by intro d hd; cases hd)))
def cl_62575 : CNF.NClause := [(126,false),(84,true)]
theorem der_62575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62575 :=
  CNF.rup_sound cl_62575 [cl_15768,cl_62416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_62416 v h) (by intro d hd; cases hd)))
def cl_62576 : CNF.NClause := [(75,true),(146,false)]
theorem der_62576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62576 :=
  CNF.rup_sound cl_62576 [cl_61588,cl_57328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61588 v h) (hints_cons _ _ _ (der_57328 v h) (by intro d hd; cases hd)))
def cl_62577 : CNF.NClause := [(75,true),(127,false)]
theorem der_62577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62577 :=
  CNF.rup_sound cl_62577 [cl_61588,cl_58916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61588 v h) (hints_cons _ _ _ (der_58916 v h) (by intro d hd; cases hd)))
def cl_62580 : CNF.NClause := [(70,true),(127,false)]
theorem der_62580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62580 :=
  CNF.rup_sound cl_62580 [cl_57480,cl_61990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57480 v h) (hints_cons _ _ _ (der_61990 v h) (by intro d hd; cases hd)))
def cl_62584 : CNF.NClause := [(142,false),(86,true)]
theorem der_62584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62584 :=
  CNF.rup_sound cl_62584 [cl_15784,cl_62411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_62411 v h) (by intro d hd; cases hd)))
def cl_62587 : CNF.NClause := [(141,false),(70,true)]
theorem der_62587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62587 :=
  CNF.rup_sound cl_62587 [cl_15783,cl_62219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_62219 v h) (by intro d hd; cases hd)))
def cl_62589 : CNF.NClause := [(135,false),(72,true)]
theorem der_62589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62589 :=
  CNF.rup_sound cl_62589 [cl_15777,cl_62209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_62209 v h) (by intro d hd; cases hd)))
def cl_62591 : CNF.NClause := [(127,false),(85,true)]
theorem der_62591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62591 :=
  CNF.rup_sound cl_62591 [cl_15769,cl_62424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_62424 v h) (by intro d hd; cases hd)))
def cl_62592 : CNF.NClause := [(63,true),(148,false)]
theorem der_62592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62592 :=
  CNF.rup_sound cl_62592 [cl_62565,cl_57788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62565 v h) (hints_cons _ _ _ (der_57788 v h) (by intro d hd; cases hd)))
def cl_62594 : CNF.NClause := [(63,true),(143,false)]
theorem der_62594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62594 :=
  CNF.rup_sound cl_62594 [cl_62565,cl_59262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62565 v h) (hints_cons _ _ _ (der_59262 v h) (by intro d hd; cases hd)))
def cl_62595 : CNF.NClause := [(72,true),(134,false)]
theorem der_62595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62595 :=
  CNF.rup_sound cl_62595 [cl_62571,cl_62589,cl_54091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62571 v h) (hints_cons _ _ _ (der_62589 v h) (hints_cons _ _ _ (der_54091 v h) (by intro d hd; cases hd))))
def cl_62596 : CNF.NClause := [(72,true),(137,false)]
theorem der_62596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62596 :=
  CNF.rup_sound cl_62596 [cl_62595,cl_62589,cl_58060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62595 v h) (hints_cons _ _ _ (der_62589 v h) (hints_cons _ _ _ (der_58060 v h) (by intro d hd; cases hd))))
def cl_62606 : CNF.NClause := [(65,true),(147,true),(127,false),(132,true)]
theorem der_62606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62606 :=
  CNF.rup_sound cl_62606 [cl_15769,cl_49758,cl_49766,cl_15784,cl_15779,cl_15635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_49758 v h) (hints_cons _ _ _ (der_49766 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_15635 v h) (by intro d hd; cases hd)))))))
def cl_62618 : CNF.NClause := [(134,false),(94,false),(119,false),(40,false),(67,false),(69,false),(20,false),(78,false),(39,true),(76,false),(153,true),(147,true),(127,false),(126,true),(112,false),(143,true),(71,false),(12,false),(72,false),(73,false),(68,false),(74,false)]
theorem der_62618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62618 :=
  CNF.rup_sound cl_62618 [cl_62559,cl_62580,cl_62577,cl_15776,cl_8043,cl_49778,cl_5249,cl_59592,cl_6529,cl_49893,cl_30832,cl_49962,cl_7946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62580 v h) (hints_cons _ _ _ (der_62577 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (inp_8043 v h) (hints_cons _ _ _ (der_49778 v h) (hints_cons _ _ _ (inp_5249 v h) (hints_cons _ _ _ (der_59592 v h) (hints_cons _ _ _ (inp_6529 v h) (hints_cons _ _ _ (der_49893 v h) (hints_cons _ _ _ (der_30832 v h) (hints_cons _ _ _ (der_49962 v h) (hints_cons _ _ _ (inp_7946 v h) (by intro d hd; cases hd))))))))))))))
def cl_62627 : CNF.NClause := [(80,true),(127,false),(3,false)]
theorem der_62627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62627 :=
  CNF.rup_sound cl_62627 [cl_61313,cl_62338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61313 v h) (hints_cons _ _ _ (der_62338 v h) (by intro d hd; cases hd)))
def cl_62639 : CNF.NClause := [(151,true),(129,true),(133,true),(143,true),(139,true),(145,true),(147,true),(125,true),(153,true),(150,true),(127,false)]
theorem der_62639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62639 :=
  CNF.rup_sound cl_62639 [cl_15618,cl_8111,cl_8085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15618 v h) (hints_cons _ _ _ (inp_8111 v h) (hints_cons _ _ _ (inp_8085 v h) (by intro d hd; cases hd))))
def cl_62641 : CNF.NClause := [(73,true),(28,false),(7,false)]
theorem der_62641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62641 :=
  CNF.rup_sound cl_62641 [cl_50068,cl_50010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50068 v h) (hints_cons _ _ _ (der_50010 v h) (by intro d hd; cases hd)))
def cl_62665 : CNF.NClause := [(128,false),(83,false),(78,false),(35,true),(3,false),(63,false),(73,false)]
theorem der_62665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62665 :=
  CNF.rup_sound cl_62665 [cl_15770,cl_54056,cl_42525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_54056 v h) (hints_cons _ _ _ (der_42525 v h) (by intro d hd; cases hd))))
def cl_62670 : CNF.NClause := [(131,false),(38,true),(71,false),(80,false),(64,false),(89,false),(73,false)]
theorem der_62670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62670 :=
  CNF.rup_sound cl_62670 [cl_15773,cl_61361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_61361 v h) (by intro d hd; cases hd)))
def cl_62672 : CNF.NClause := [(74,true),(143,false),(10,true)]
theorem der_62672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62672 :=
  CNF.rup_sound cl_62672 [cl_15785,cl_49566,cl_62314,cl_50169,cl_15789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_49566 v h) (hints_cons _ _ _ (der_62314 v h) (hints_cons _ _ _ (der_50169 v h) (hints_cons _ _ _ (der_15789 v h) (by intro d hd; cases hd))))))
def cl_62677 : CNF.NClause := [(65,true),(132,true),(127,false)]
theorem der_62677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62677 :=
  CNF.rup_sound cl_62677 [cl_15769,cl_49831,cl_62606,cl_15789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_49831 v h) (hints_cons _ _ _ (der_62606 v h) (hints_cons _ _ _ (der_15789 v h) (by intro d hd; cases hd)))))
def cl_62678 : CNF.NClause := [(125,false),(54,true),(104,false),(115,false),(65,false),(76,false),(93,false),(121,false),(71,false),(81,false),(80,false),(70,false),(75,false),(3,false),(85,false),(66,false),(59,false)]
theorem der_62678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62678 :=
  CNF.rup_sound cl_62678 [cl_15767,cl_62566,cl_57334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_62566 v h) (hints_cons _ _ _ (der_57334 v h) (by intro d hd; cases hd))))
def cl_62682 : CNF.NClause := [(129,false),(40,true),(130,true),(131,true),(132,true),(69,false),(81,false),(75,false),(17,false)]
theorem der_62682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62682 :=
  CNF.rup_sound cl_62682 [cl_62455,cl_15660,cl_62333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62455 v h) (hints_cons _ _ _ (der_15660 v h) (hints_cons _ _ _ (der_62333 v h) (by intro d hd; cases hd))))
def cl_62683 : CNF.NClause := [(23,false),(54,true),(67,false),(65,false),(81,false),(74,false),(11,true),(89,false),(17,false)]
theorem der_62683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62683 :=
  CNF.rup_sound cl_62683 [cl_54101,cl_6913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54101 v h) (hints_cons _ _ _ (inp_6913 v h) (by intro d hd; cases hd)))
def cl_62684 : CNF.NClause := [(142,false),(49,true),(65,false),(69,false),(77,false),(12,false),(73,false)]
theorem der_62684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62684 :=
  CNF.rup_sound cl_62684 [cl_15784,cl_49886,cl_6273,cl_62584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_49886 v h) (hints_cons _ _ _ (inp_6273 v h) (hints_cons _ _ _ (der_62584 v h) (by intro d hd; cases hd)))))
def cl_62690 : CNF.NClause := [(83,true),(23,true),(4,false),(11,true),(17,false)]
theorem der_62690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62690 :=
  CNF.rup_sound cl_62690 [cl_54102,cl_54103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54102 v h) (hints_cons _ _ _ (der_54103 v h) (by intro d hd; cases hd)))
def cl_62696 : CNF.NClause := [(67,true),(144,false)]
theorem der_62696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62696 :=
  CNF.rup_sound cl_62696 [cl_15786,cl_43960,cl_49872,cl_61975,cl_36151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_43960 v h) (hints_cons _ _ _ (der_49872 v h) (hints_cons _ _ _ (der_61975 v h) (hints_cons _ _ _ (der_36151 v h) (by intro d hd; cases hd))))))
def cl_62702 : CNF.NClause := [(34,false),(97,false),(99,false),(120,false),(47,false),(104,false),(93,false),(50,false),(59,false)]
theorem der_62702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62702 :=
  CNF.rup_sound cl_62702 [cl_62561,cl_58527,cl_61940,cl_50033,cl_43027,cl_7965,cl_7953,cl_43031,cl_50265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_58527 v h) (hints_cons _ _ _ (der_61940 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_43027 v h) (hints_cons _ _ _ (inp_7965 v h) (hints_cons _ _ _ (inp_7953 v h) (hints_cons _ _ _ (der_43031 v h) (hints_cons _ _ _ (der_50265 v h) (by intro d hd; cases hd))))))))))
def cl_62705 : CNF.NClause := [(79,true),(145,true),(132,false)]
theorem der_62705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62705 :=
  CNF.rup_sound cl_62705 [cl_15774,cl_37816,cl_57826,cl_50065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_37816 v h) (hints_cons _ _ _ (der_57826 v h) (hints_cons _ _ _ (der_50065 v h) (by intro d hd; cases hd)))))
def cl_62741 : CNF.NClause := [(91,true),(72,true),(12,false)]
theorem der_62741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62741 :=
  CNF.rup_sound cl_62741 [cl_46318,cl_13749,cl_15836,cl_49832,cl_14196,cl_49818,cl_14197,cl_48585,cl_14199,cl_10633,cl_15834,cl_37342,cl_49974,cl_49886,cl_50102,cl_14192,cl_14209,cl_14203,cl_14211,cl_10749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46318 v h) (hints_cons _ _ _ (inp_13749 v h) (hints_cons _ _ _ (der_15836 v h) (hints_cons _ _ _ (der_49832 v h) (hints_cons _ _ _ (inp_14196 v h) (hints_cons _ _ _ (der_49818 v h) (hints_cons _ _ _ (inp_14197 v h) (hints_cons _ _ _ (der_48585 v h) (hints_cons _ _ _ (inp_14199 v h) (hints_cons _ _ _ (inp_10633 v h) (hints_cons _ _ _ (der_15834 v h) (hints_cons _ _ _ (der_37342 v h) (hints_cons _ _ _ (der_49974 v h) (hints_cons _ _ _ (der_49886 v h) (hints_cons _ _ _ (der_50102 v h) (hints_cons _ _ _ (inp_14192 v h) (hints_cons _ _ _ (inp_14209 v h) (hints_cons _ _ _ (inp_14203 v h) (hints_cons _ _ _ (inp_14211 v h) (hints_cons _ _ _ (inp_10749 v h) (by intro d hd; cases hd)))))))))))))))))))))
def cl_62747 : CNF.NClause := [(94,true),(50,false),(55,false),(45,true)]
theorem der_62747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62747 :=
  CNF.rup_sound cl_62747 [cl_61489,cl_31688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61489 v h) (hints_cons _ _ _ (der_31688 v h) (by intro d hd; cases hd)))
def cl_62752 : CNF.NClause := [(71,true),(143,false),(13,true)]
theorem der_62752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62752 :=
  CNF.rup_sound cl_62752 [cl_15785,cl_49564,cl_61933,cl_59881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_49564 v h) (hints_cons _ _ _ (der_61933 v h) (hints_cons _ _ _ (der_59881 v h) (by intro d hd; cases hd)))))
def cl_62787 : CNF.NClause := [(4,false),(35,true),(68,false),(23,true),(78,false),(3,false),(63,false),(11,true),(17,false),(73,false)]
theorem der_62787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62787 :=
  CNF.rup_sound cl_62787 [cl_42525,cl_62690,cl_4481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42525 v h) (hints_cons _ _ _ (der_62690 v h) (hints_cons _ _ _ (inp_4481 v h) (by intro d hd; cases hd))))
def cl_62789 : CNF.NClause := [(67,true),(24,false),(21,false)]
theorem der_62789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62789 :=
  CNF.rup_sound cl_62789 [cl_49876,cl_50211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49876 v h) (hints_cons _ _ _ (der_50211 v h) (by intro d hd; cases hd)))
def cl_62806 : CNF.NClause := [(68,true),(1066,false),(12,false)]
theorem der_62806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62806 :=
  CNF.rup_sound cl_62806 [cl_50009,cl_50536,cl_49989,cl_50184,cl_49820,cl_15926,cl_15914,cl_15910,cl_15922,cl_15934,cl_13587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50009 v h) (hints_cons _ _ _ (der_50536 v h) (hints_cons _ _ _ (der_49989 v h) (hints_cons _ _ _ (der_50184 v h) (hints_cons _ _ _ (der_49820 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_15910 v h) (hints_cons _ _ _ (der_15922 v h) (hints_cons _ _ _ (der_15934 v h) (hints_cons _ _ _ (inp_13587 v h) (by intro d hd; cases hd))))))))))))
def cl_62836 : CNF.NClause := [(65,true),(127,false)]
theorem der_62836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62836 :=
  CNF.rup_sound cl_62836 [cl_60459,cl_62677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60459 v h) (hints_cons _ _ _ (der_62677 v h) (by intro d hd; cases hd)))
def cl_62857 : CNF.NClause := [(113,true),(37,false),(38,false)]
theorem der_62857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62857 :=
  CNF.rup_sound cl_62857 [cl_62559,cl_30836,cl_56265,cl_53661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_30836 v h) (hints_cons _ _ _ (der_56265 v h) (hints_cons _ _ _ (der_53661 v h) (by intro d hd; cases hd)))))
def cl_62871 : CNF.NClause := [(2,false),(33,true),(26,false),(69,false),(3,false),(74,false),(84,false),(14,true),(12,false)]
theorem der_62871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62871 :=
  CNF.rup_sound cl_62871 [cl_49790,cl_61702,cl_53840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49790 v h) (hints_cons _ _ _ (der_61702 v h) (hints_cons _ _ _ (der_53840 v h) (by intro d hd; cases hd))))
def cl_62873 : CNF.NClause := [(113,true),(37,false),(40,false)]
theorem der_62873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62873 :=
  CNF.rup_sound cl_62873 [cl_62559,cl_30832,cl_56265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_30832 v h) (hints_cons _ _ _ (der_56265 v h) (by intro d hd; cases hd))))
def cl_62886 : CNF.NClause := [(79,true),(26,false),(21,false),(14,true)]
theorem der_62886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62886 :=
  CNF.rup_sound cl_62886 [cl_50141,cl_53840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50141 v h) (hints_cons _ _ _ (der_53840 v h) (by intro d hd; cases hd)))
def cl_62898 : CNF.NClause := [(78,true),(130,false),(6,false),(13,true)]
theorem der_62898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62898 :=
  CNF.rup_sound cl_62898 [cl_62286,cl_37513,cl_59248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_37513 v h) (hints_cons _ _ _ (der_59248 v h) (by intro d hd; cases hd))))
def cl_62905 : CNF.NClause := [(46,false),(15,true),(77,false),(80,false),(81,false)]
theorem der_62905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62905 :=
  CNF.rup_sound cl_62905 [cl_32896,cl_50911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32896 v h) (hints_cons _ _ _ (der_50911 v h) (by intro d hd; cases hd)))
def cl_62910 : CNF.NClause := [(98,true),(55,false),(54,false)]
theorem der_62910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62910 :=
  CNF.rup_sound cl_62910 [cl_50364,cl_50365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50364 v h) (hints_cons _ _ _ (der_50365 v h) (by intro d hd; cases hd)))
def cl_62911 : CNF.NClause := [(55,false),(94,false),(32,false),(34,false),(49,false),(54,false),(59,false)]
theorem der_62911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62911 :=
  CNF.rup_sound cl_62911 [cl_62561,cl_49964,cl_58294,cl_49969,cl_55963,cl_7961,cl_62910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_49964 v h) (hints_cons _ _ _ (der_58294 v h) (hints_cons _ _ _ (der_49969 v h) (hints_cons _ _ _ (der_55963 v h) (hints_cons _ _ _ (inp_7961 v h) (hints_cons _ _ _ (der_62910 v h) (by intro d hd; cases hd))))))))
def cl_62914 : CNF.NClause := [(111,true),(94,false),(116,false),(32,false),(34,false),(49,false),(105,false),(121,false),(50,false)]
theorem der_62914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62914 :=
  CNF.rup_sound cl_62914 [cl_62559,cl_42523,cl_49842,cl_58002,cl_50093,cl_7956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_42523 v h) (hints_cons _ _ _ (der_49842 v h) (hints_cons _ _ _ (der_58002 v h) (hints_cons _ _ _ (der_50093 v h) (hints_cons _ _ _ (inp_7956 v h) (by intro d hd; cases hd)))))))
def cl_62926 : CNF.NClause := [(146,false),(86,true),(138,true)]
theorem der_62926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62926 :=
  CNF.rup_sound cl_62926 [cl_15788,cl_48288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_48288 v h) (by intro d hd; cases hd)))
def cl_62957 : CNF.NClause := [(113,true),(38,false),(40,false)]
theorem der_62957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62957 :=
  CNF.rup_sound cl_62957 [cl_62559,cl_62857,cl_60491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62857 v h) (hints_cons _ _ _ (der_60491 v h) (by intro d hd; cases hd))))
def cl_62965 : CNF.NClause := [(4,false),(35,true),(78,false),(83,false),(3,false),(63,false),(68,false),(73,false)]
theorem der_62965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62965 :=
  CNF.rup_sound cl_62965 [cl_42525,cl_4481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42525 v h) (hints_cons _ _ _ (inp_4481 v h) (by intro d hd; cases hd)))
def cl_62974 : CNF.NClause := [(108,true),(47,false),(50,false)]
theorem der_62974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62974 :=
  CNF.rup_sound cl_62974 [cl_62559,cl_45747,cl_50265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_45747 v h) (hints_cons _ _ _ (der_50265 v h) (by intro d hd; cases hd))))
def cl_62981 : CNF.NClause := [(130,false),(78,true),(13,true)]
theorem der_62981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62981 :=
  CNF.rup_sound cl_62981 [cl_15772,cl_62898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_62898 v h) (by intro d hd; cases hd)))
def cl_62986 : CNF.NClause := [(60,false),(109,false),(96,false),(116,false),(101,false),(34,false),(114,false),(104,false),(35,false),(42,true),(50,false)]
theorem der_62986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62986 :=
  CNF.rup_sound cl_62986 [cl_62561,cl_62559,cl_42604,cl_50085,cl_49975,cl_7940,cl_7941,cl_49856,cl_54924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_42604 v h) (hints_cons _ _ _ (der_50085 v h) (hints_cons _ _ _ (der_49975 v h) (hints_cons _ _ _ (inp_7940 v h) (hints_cons _ _ _ (inp_7941 v h) (hints_cons _ _ _ (der_49856 v h) (hints_cons _ _ _ (der_54924 v h) (by intro d hd; cases hd))))))))))
def cl_62991 : CNF.NClause := [(79,true),(150,false),(126,true),(132,true),(138,true)]
theorem der_62991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_62991 :=
  CNF.rup_sound cl_62991 [cl_15791,cl_56741,cl_49936,cl_8070,cl_15781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_56741 v h) (hints_cons _ _ _ (der_49936 v h) (hints_cons _ _ _ (inp_8070 v h) (hints_cons _ _ _ (der_15781 v h) (by intro d hd; cases hd))))))
def cl_63010 : CNF.NClause := [(76,true),(24,false),(10,true),(17,false)]
theorem der_63010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63010 :=
  CNF.rup_sound cl_63010 [cl_50168,cl_50127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50168 v h) (hints_cons _ _ _ (der_50127 v h) (by intro d hd; cases hd)))
def cl_63026 : CNF.NClause := [(15,false),(4,false),(78,true)]
theorem der_63026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63026 :=
  CNF.rup_sound cl_63026 [cl_50421,cl_50196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50421 v h) (hints_cons _ _ _ (der_50196 v h) (by intro d hd; cases hd)))
def cl_63027 : CNF.NClause := [(139,false),(78,true)]
theorem der_63027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63027 :=
  CNF.rup_sound cl_63027 [cl_62286,cl_61644,cl_15781,cl_57845,cl_63026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_61644 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_57845 v h) (hints_cons _ _ _ (der_63026 v h) (by intro d hd; cases hd))))))
def cl_63039 : CNF.NClause := [(126,false),(33,true),(69,false),(15,false),(131,true),(3,false),(74,false),(84,false)]
theorem der_63039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63039 :=
  CNF.rup_sound cl_63039 [cl_62507,cl_59419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62507 v h) (hints_cons _ _ _ (der_59419 v h) (by intro d hd; cases hd)))
def cl_63040 : CNF.NClause := [(147,false),(67,true)]
theorem der_63040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63040 :=
  CNF.rup_sound cl_63040 [cl_15789,cl_61974,cl_35629,cl_15788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_61974 v h) (hints_cons _ _ _ (der_35629 v h) (hints_cons _ _ _ (der_15788 v h) (by intro d hd; cases hd)))))
def cl_63041 : CNF.NClause := [(94,true),(35,false),(50,false),(45,true)]
theorem der_63041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63041 :=
  CNF.rup_sound cl_63041 [cl_61489,cl_54924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61489 v h) (hints_cons _ _ _ (der_54924 v h) (by intro d hd; cases hd)))
def cl_63052 : CNF.NClause := [(153,false),(94,false),(105,false),(83,false),(116,false),(76,false),(1,false),(38,true),(121,false),(50,false),(81,false),(70,false),(3,false),(71,false),(77,false),(66,false),(64,false),(17,false)]
theorem der_63052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63052 :=
  CNF.rup_sound cl_63052 [cl_62559,cl_15794,cl_57227,cl_49908,cl_57424,cl_6145,cl_50093,cl_48917,cl_7956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_57227 v h) (hints_cons _ _ _ (der_49908 v h) (hints_cons _ _ _ (der_57424 v h) (hints_cons _ _ _ (inp_6145 v h) (hints_cons _ _ _ (der_50093 v h) (hints_cons _ _ _ (der_48917 v h) (hints_cons _ _ _ (inp_7956 v h) (by intro d hd; cases hd))))))))))
def cl_63068 : CNF.NClause := [(151,false),(69,false),(76,false),(58,true),(85,false),(89,false)]
theorem der_63068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63068 :=
  CNF.rup_sound cl_63068 [cl_61644,cl_38351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61644 v h) (hints_cons _ _ _ (der_38351 v h) (by intro d hd; cases hd)))
def cl_63071 : CNF.NClause := [(67,true),(146,false)]
theorem der_63071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63071 :=
  CNF.rup_sound cl_63071 [cl_15788,cl_61972,cl_49876,cl_15787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_61972 v h) (hints_cons _ _ _ (der_49876 v h) (hints_cons _ _ _ (der_15787 v h) (by intro d hd; cases hd)))))
def cl_63080 : CNF.NClause := [(88,true),(141,true),(17,false)]
theorem der_63080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63080 :=
  CNF.rup_sound cl_63080 [cl_49839,cl_50493,cl_15787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49839 v h) (hints_cons _ _ _ (der_50493 v h) (hints_cons _ _ _ (der_15787 v h) (by intro d hd; cases hd))))
def cl_63081 : CNF.NClause := [(79,true),(132,false)]
theorem der_63081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63081 :=
  CNF.rup_sound cl_63081 [cl_56741,cl_62705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56741 v h) (hints_cons _ _ _ (der_62705 v h) (by intro d hd; cases hd)))
def cl_63096 : CNF.NClause := [(83,true),(147,true),(4,true),(141,false),(11,true),(135,true),(17,false)]
theorem der_63096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63096 :=
  CNF.rup_sound cl_63096 [cl_15770,cl_30245,cl_49014,cl_15791,cl_8096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_30245 v h) (hints_cons _ _ _ (der_49014 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (inp_8096 v h) (by intro d hd; cases hd))))))
def cl_63163 : CNF.NClause := [(148,false),(67,true),(76,false),(80,false),(63,false),(84,false),(91,false)]
theorem der_63163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63163 :=
  CNF.rup_sound cl_63163 [cl_63040,cl_50880,cl_15790,cl_52880,cl_49891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63040 v h) (hints_cons _ _ _ (der_50880 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_52880 v h) (hints_cons _ _ _ (der_49891 v h) (by intro d hd; cases hd))))))
def cl_63179 : CNF.NClause := [(112,true),(40,false),(59,false)]
theorem der_63179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63179 :=
  CNF.rup_sound cl_63179 [cl_49939,cl_50382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49939 v h) (hints_cons _ _ _ (der_50382 v h) (by intro d hd; cases hd)))
def cl_63185 : CNF.NClause := [(35,false),(53,false),(54,false),(34,false),(39,false),(50,false),(45,true),(41,true),(59,false)]
theorem der_63185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63185 :=
  CNF.rup_sound cl_63185 [cl_62559,cl_62561,cl_50453,cl_42577,cl_42604,cl_63041,cl_49882,cl_35634,cl_7941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50453 v h) (hints_cons _ _ _ (der_42577 v h) (hints_cons _ _ _ (der_42604 v h) (hints_cons _ _ _ (der_63041 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (inp_7941 v h) (by intro d hd; cases hd))))))))))
def cl_63192 : CNF.NClause := [(78,true),(151,true),(146,false),(13,true)]
theorem der_63192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63192 :=
  CNF.rup_sound cl_63192 [cl_15788,cl_62286,cl_58736,cl_37513,cl_50486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_58736 v h) (hints_cons _ _ _ (der_37513 v h) (hints_cons _ _ _ (der_50486 v h) (by intro d hd; cases hd))))))
def cl_63197 : CNF.NClause := [(49,false),(69,true),(65,false),(77,false),(91,false),(73,false)]
theorem der_63197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63197 :=
  CNF.rup_sound cl_63197 [cl_52701,cl_49717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52701 v h) (hints_cons _ _ _ (der_49717 v h) (by intro d hd; cases hd)))
def cl_63208 : CNF.NClause := [(35,true),(4,false),(78,false),(3,false),(63,false),(68,false),(11,true),(17,false),(73,false)]
theorem der_63208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63208 :=
  CNF.rup_sound cl_63208 [cl_62965,cl_62787,cl_54102,cl_51527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_62787 v h) (hints_cons _ _ _ (der_54102 v h) (hints_cons _ _ _ (der_51527 v h) (by intro d hd; cases hd)))))
def cl_63248 : CNF.NClause := [(27,false),(9,false),(76,false),(58,true),(28,false),(78,false),(85,false),(89,false)]
theorem der_63248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63248 :=
  CNF.rup_sound cl_63248 [cl_37308,cl_54627,cl_53736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37308 v h) (hints_cons _ _ _ (der_54627 v h) (hints_cons _ _ _ (der_53736 v h) (by intro d hd; cases hd))))
def cl_63255 : CNF.NClause := [(76,true),(482,false),(10,true),(11,true),(17,false)]
theorem der_63255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63255 :=
  CNF.rup_sound cl_63255 [cl_14106,cl_50168,cl_50127,cl_42519,cl_50442,cl_14097,cl_14119,cl_14122,cl_14104,cl_10100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14106 v h) (hints_cons _ _ _ (der_50168 v h) (hints_cons _ _ _ (der_50127 v h) (hints_cons _ _ _ (der_42519 v h) (hints_cons _ _ _ (der_50442 v h) (hints_cons _ _ _ (inp_14097 v h) (hints_cons _ _ _ (inp_14119 v h) (hints_cons _ _ _ (inp_14122 v h) (hints_cons _ _ _ (inp_14104 v h) (hints_cons _ _ _ (inp_10100 v h) (by intro d hd; cases hd)))))))))))
def cl_63328 : CNF.NClause := [(23,false),(54,true),(81,false),(3,false),(67,false),(74,false),(11,true),(89,false),(17,false)]
theorem der_63328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63328 :=
  CNF.rup_sound cl_63328 [cl_49831,cl_62683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49831 v h) (hints_cons _ _ _ (der_62683 v h) (by intro d hd; cases hd)))
def cl_63356 : CNF.NClause := [(65,false),(82,false),(39,true),(76,false),(23,true),(79,false),(3,true),(19,false),(68,false),(13,true)]
theorem der_63356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63356 :=
  CNF.rup_sound cl_63356 [cl_58418,cl_23277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58418 v h) (hints_cons _ _ _ (der_23277 v h) (by intro d hd; cases hd)))
def cl_63359 : CNF.NClause := [(126,false),(33,true),(4,false),(131,true),(69,false),(79,false),(74,false),(84,false)]
theorem der_63359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63359 :=
  CNF.rup_sound cl_63359 [cl_15768,cl_59184,cl_58713,cl_23170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_59184 v h) (hints_cons _ _ _ (der_58713 v h) (hints_cons _ _ _ (der_23170 v h) (by intro d hd; cases hd)))))
def cl_63367 : CNF.NClause := [(83,true),(26,false),(23,true),(11,true),(17,false)]
theorem der_63367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63367 :=
  CNF.rup_sound cl_63367 [cl_62690,cl_30245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62690 v h) (hints_cons _ _ _ (der_30245 v h) (by intro d hd; cases hd)))
def cl_63372 : CNF.NClause := [(80,true),(29,false),(7,false),(3,true)]
theorem der_63372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63372 :=
  CNF.rup_sound cl_63372 [cl_61117,cl_30462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61117 v h) (hints_cons _ _ _ (der_30462 v h) (by intro d hd; cases hd)))
def cl_63385 : CNF.NClause := [(120,true),(38,false),(58,false),(45,true)]
theorem der_63385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63385 :=
  CNF.rup_sound cl_63385 [cl_62561,cl_50818,cl_50814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50818 v h) (hints_cons _ _ _ (der_50814 v h) (by intro d hd; cases hd))))
def cl_63400 : CNF.NClause := [(47,false),(43,false),(37,false),(50,false),(53,false),(59,false),(58,false)]
theorem der_63400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63400 :=
  CNF.rup_sound cl_63400 [cl_62561,cl_50046,cl_58527,cl_62974,cl_57601,cl_50492,cl_57663,cl_7953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50046 v h) (hints_cons _ _ _ (der_58527 v h) (hints_cons _ _ _ (der_62974 v h) (hints_cons _ _ _ (der_57601 v h) (hints_cons _ _ _ (der_50492 v h) (hints_cons _ _ _ (der_57663 v h) (hints_cons _ _ _ (inp_7953 v h) (by intro d hd; cases hd)))))))))
def cl_63405 : CNF.NClause := [(65,true),(142,false)]
theorem der_63405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63405 :=
  CNF.rup_sound cl_63405 [cl_15784,cl_49758,cl_41935,cl_49807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_49758 v h) (hints_cons _ _ _ (der_41935 v h) (hints_cons _ _ _ (der_49807 v h) (by intro d hd; cases hd)))))
def cl_63419 : CNF.NClause := [(147,false),(142,true),(54,true),(11,true),(67,false),(17,false),(81,false),(89,false),(74,false)]
theorem der_63419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63419 :=
  CNF.rup_sound cl_63419 [cl_15789,cl_63328,cl_62683,cl_15769,cl_61203,cl_60459,cl_15631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_63328 v h) (hints_cons _ _ _ (der_62683 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_61203 v h) (hints_cons _ _ _ (der_60459 v h) (hints_cons _ _ _ (der_15631 v h) (by intro d hd; cases hd))))))))
def cl_63439 : CNF.NClause := [(16,false),(140,true),(147,true),(89,true),(14,true)]
theorem der_63439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63439 :=
  CNF.rup_sound cl_63439 [cl_15780,cl_50076,cl_49824,cl_15773,cl_15792,cl_15663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_50076 v h) (hints_cons _ _ _ (der_49824 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_15663 v h) (by intro d hd; cases hd)))))))
def cl_63458 : CNF.NClause := [(95,true),(53,false),(43,false)]
theorem der_63458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63458 :=
  CNF.rup_sound cl_63458 [cl_55114,cl_54934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55114 v h) (hints_cons _ _ _ (der_54934 v h) (by intro d hd; cases hd)))
def cl_63459 : CNF.NClause := [(74,true),(19,false),(29,false)]
theorem der_63459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63459 :=
  CNF.rup_sound cl_63459 [cl_49566,cl_62355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49566 v h) (hints_cons _ _ _ (der_62355 v h) (by intro d hd; cases hd)))
def cl_63461 : CNF.NClause := [(65,true),(146,false),(131,true),(129,true),(140,true),(150,true),(130,true),(134,true)]
theorem der_63461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63461 :=
  CNF.rup_sound cl_63461 [cl_60459,cl_62836,cl_15656,cl_8047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60459 v h) (hints_cons _ _ _ (der_62836 v h) (hints_cons _ _ _ (der_15656 v h) (hints_cons _ _ _ (inp_8047 v h) (by intro d hd; cases hd)))))
def cl_63464 : CNF.NClause := [(103,true),(41,true),(43,false),(45,false)]
theorem der_63464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63464 :=
  CNF.rup_sound cl_63464 [cl_31625,cl_42423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31625 v h) (hints_cons _ _ _ (der_42423 v h) (by intro d hd; cases hd)))
def cl_63466 : CNF.NClause := [(103,true),(45,false),(44,true),(43,false)]
theorem der_63466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63466 :=
  CNF.rup_sound cl_63466 [cl_63464,cl_43523,cl_48629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63464 v h) (hints_cons _ _ _ (der_43523 v h) (hints_cons _ _ _ (der_48629 v h) (by intro d hd; cases hd))))
def cl_63467 : CNF.NClause := [(76,true),(27,false),(1,false)]
theorem der_63467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63467 :=
  CNF.rup_sound cl_63467 [cl_56755,cl_50166,cl_51561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56755 v h) (hints_cons _ _ _ (der_50166 v h) (hints_cons _ _ _ (der_51561 v h) (by intro d hd; cases hd))))
def cl_63479 : CNF.NClause := [(146,false),(19,false),(75,false),(78,false),(64,false),(53,true),(86,false)]
theorem der_63479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63479 :=
  CNF.rup_sound cl_63479 [cl_15788,cl_40644,cl_49803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_40644 v h) (hints_cons _ _ _ (der_49803 v h) (by intro d hd; cases hd))))
def cl_63480 : CNF.NClause := [(71,true),(143,false)]
theorem der_63480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63480 :=
  CNF.rup_sound cl_63480 [cl_15785,cl_62752,cl_61981,cl_50118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_62752 v h) (hints_cons _ _ _ (der_61981 v h) (hints_cons _ _ _ (der_50118 v h) (by intro d hd; cases hd)))))
def cl_63482 : CNF.NClause := [(92,true),(83,false),(86,false),(36,false),(85,false)]
theorem der_63482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63482 :=
  CNF.rup_sound cl_63482 [cl_52187,cl_52184,cl_52188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52187 v h) (hints_cons _ _ _ (der_52184 v h) (hints_cons _ _ _ (der_52188 v h) (by intro d hd; cases hd))))
def cl_63490 : CNF.NClause := [(71,true),(137,false),(13,false)]
theorem der_63490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63490 :=
  CNF.rup_sound cl_63490 [cl_61292,cl_61981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61292 v h) (hints_cons _ _ _ (der_61981 v h) (by intro d hd; cases hd)))
def cl_63501 : CNF.NClause := [(8,true),(14,true),(15,true),(79,false),(21,true),(2,true)]
theorem der_63501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63501 :=
  CNF.rup_sound cl_63501 [cl_53786,cl_1120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53786 v h) (hints_cons _ _ _ (inp_1120 v h) (by intro d hd; cases hd)))
def cl_63502 : CNF.NClause := [(10,false),(8,false),(41,true),(74,false),(17,true),(75,false),(72,false),(5,false),(73,false)]
theorem der_63502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63502 :=
  CNF.rup_sound cl_63502 [cl_37437,cl_5249,cl_50122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37437 v h) (hints_cons _ _ _ (inp_5249 v h) (hints_cons _ _ _ (der_50122 v h) (by intro d hd; cases hd))))
def cl_63516 : CNF.NClause := [(1070,false),(84,false),(47,true),(89,false),(18,false),(68,false),(75,false),(1065,true)]
theorem der_63516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63516 :=
  CNF.rup_sound cl_63516 [cl_15922,cl_52752,cl_49869,cl_49788,cl_49804,cl_15907,cl_15912,cl_15927,cl_15734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15922 v h) (hints_cons _ _ _ (der_52752 v h) (hints_cons _ _ _ (der_49869 v h) (hints_cons _ _ _ (der_49788 v h) (hints_cons _ _ _ (der_49804 v h) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_15927 v h) (hints_cons _ _ _ (der_15734 v h) (by intro d hd; cases hd))))))))))
def cl_63517 : CNF.NClause := [(64,true),(141,true),(146,false),(22,false)]
theorem der_63517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63517 :=
  CNF.rup_sound cl_63517 [cl_49795,cl_56922,cl_15773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49795 v h) (hints_cons _ _ _ (der_56922 v h) (hints_cons _ _ _ (der_15773 v h) (by intro d hd; cases hd))))
def cl_63525 : CNF.NClause := [(92,false),(76,false),(74,false),(41,true),(72,false),(20,true),(15,true),(73,false),(75,false)]
theorem der_63525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63525 :=
  CNF.rup_sound cl_63525 [cl_29784,cl_5249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29784 v h) (hints_cons _ _ _ (inp_5249 v h) (by intro d hd; cases hd)))
def cl_63531 : CNF.NClause := [(19,false),(141,true),(74,true),(138,true),(142,true),(151,true),(139,true),(131,true)]
theorem der_63531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63531 :=
  CNF.rup_sound cl_63531 [cl_63459,cl_50169,cl_50106,cl_15789,cl_62672,cl_15663,cl_15654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63459 v h) (hints_cons _ _ _ (der_50169 v h) (hints_cons _ _ _ (der_50106 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_62672 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15654 v h) (by intro d hd; cases hd))))))))
def cl_63532 : CNF.NClause := [(141,true),(74,true),(138,true),(142,true),(151,true),(126,true),(139,true),(131,true)]
theorem der_63532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63532 :=
  CNF.rup_sound cl_63532 [cl_63531,cl_15785,cl_15654,cl_15663,cl_15789,cl_42451,cl_50171,cl_50105,cl_15772,cl_15794,cl_15776,cl_8041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63531 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_15654 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_42451 v h) (hints_cons _ _ _ (der_50171 v h) (hints_cons _ _ _ (der_50105 v h) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (inp_8041 v h) (by intro d hd; cases hd)))))))))))))
def cl_63559 : CNF.NClause := [(132,false),(39,true),(68,false),(76,false),(9,true),(90,false)]
theorem der_63559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63559 :=
  CNF.rup_sound cl_63559 [cl_60459,cl_63081,cl_44602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60459 v h) (hints_cons _ _ _ (der_63081 v h) (hints_cons _ _ _ (der_44602 v h) (by intro d hd; cases hd))))
def cl_63561 : CNF.NClause := [(33,false),(84,false),(74,false),(69,true),(64,false)]
theorem der_63561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63561 :=
  CNF.rup_sound cl_63561 [cl_51104,cl_51099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51104 v h) (hints_cons _ _ _ (der_51099 v h) (by intro d hd; cases hd)))
def cl_63563 : CNF.NClause := [(68,true),(140,false),(29,true),(20,true)]
theorem der_63563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63563 :=
  CNF.rup_sound cl_63563 [cl_15782,cl_51534,cl_49402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_51534 v h) (hints_cons _ _ _ (der_49402 v h) (by intro d hd; cases hd))))
def cl_63577 : CNF.NClause := [(5,false),(36,true),(82,false),(84,false),(83,false),(85,false),(10,false),(86,false)]
theorem der_63577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63577 :=
  CNF.rup_sound cl_63577 [cl_37437,cl_4609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37437 v h) (hints_cons _ _ _ (inp_4609 v h) (by intro d hd; cases hd)))
def cl_63581 : CNF.NClause := [(91,true),(142,true),(18,false)]
theorem der_63581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63581 :=
  CNF.rup_sound cl_63581 [cl_49886,cl_49776,cl_49794,cl_49814,cl_15778,cl_15790,cl_15772,cl_15791,cl_15665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49886 v h) (hints_cons _ _ _ (der_49776 v h) (hints_cons _ _ _ (der_49794 v h) (hints_cons _ _ _ (der_49814 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15665 v h) (by intro d hd; cases hd))))))))))
def cl_63584 : CNF.NClause := [(65,true),(917,true),(18,false)]
theorem der_63584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63584 :=
  CNF.rup_sound cl_63584 [cl_49829,cl_49807,cl_49758,cl_50078,cl_15889,cl_15874,cl_15869,cl_15879,cl_15670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49829 v h) (hints_cons _ _ _ (der_49807 v h) (hints_cons _ _ _ (der_49758 v h) (hints_cons _ _ _ (der_50078 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_15670 v h) (by intro d hd; cases hd))))))))))
def cl_63585 : CNF.NClause := [(83,true),(141,false),(11,true)]
theorem der_63585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63585 :=
  CNF.rup_sound cl_63585 [cl_15783,cl_15777,cl_54102,cl_51527,cl_62690,cl_15789,cl_63096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_54102 v h) (hints_cons _ _ _ (der_51527 v h) (hints_cons _ _ _ (der_62690 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_63096 v h) (by intro d hd; cases hd))))))))
def cl_63594 : CNF.NClause := [(83,true),(4,false),(23,false),(11,true)]
theorem der_63594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63594 :=
  CNF.rup_sound cl_63594 [cl_54211,cl_51527,cl_61359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54211 v h) (hints_cons _ _ _ (der_51527 v h) (hints_cons _ _ _ (der_61359 v h) (by intro d hd; cases hd))))
def cl_63604 : CNF.NClause := [(49,false),(73,false),(65,false),(91,false),(69,true),(18,false),(86,false)]
theorem der_63604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63604 :=
  CNF.rup_sound cl_63604 [cl_34700,cl_63197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34700 v h) (hints_cons _ _ _ (der_63197 v h) (by intro d hd; cases hd)))
def cl_63620 : CNF.NClause := [(83,true),(4,true),(147,false),(141,true),(11,true)]
theorem der_63620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63620 :=
  CNF.rup_sound cl_63620 [cl_15770,cl_15789,cl_15777,cl_30243,cl_49014,cl_15791,cl_8095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_30243 v h) (hints_cons _ _ _ (der_49014 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (inp_8095 v h) (by intro d hd; cases hd))))))))
def cl_63622 : CNF.NClause := [(34,false),(87,true),(3,true),(85,false),(65,false),(75,false)]
theorem der_63622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63622 :=
  CNF.rup_sound cl_63622 [cl_52396,cl_33114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52396 v h) (hints_cons _ _ _ (der_33114 v h) (by intro d hd; cases hd)))
def cl_63629 : CNF.NClause := [(147,false),(1,true),(81,true),(133,true),(139,true)]
theorem der_63629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63629 :=
  CNF.rup_sound cl_63629 [cl_61806,cl_61053,cl_15789,cl_8083,cl_61627,cl_15793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61806 v h) (hints_cons _ _ _ (der_61053 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (inp_8083 v h) (hints_cons _ _ _ (der_61627 v h) (hints_cons _ _ _ (der_15793 v h) (by intro d hd; cases hd)))))))
def cl_63631 : CNF.NClause := [(147,false),(81,true),(133,true),(15,true)]
theorem der_63631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63631 :=
  CNF.rup_sound cl_63631 [cl_15781,cl_15789,cl_63629,cl_50456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_63629 v h) (hints_cons _ _ _ (der_50456 v h) (by intro d hd; cases hd)))))
def cl_63645 : CNF.NClause := [(76,true),(17,false),(24,false)]
theorem der_63645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63645 :=
  CNF.rup_sound cl_63645 [cl_59468,cl_63010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59468 v h) (hints_cons _ _ _ (der_63010 v h) (by intro d hd; cases hd)))
def cl_63651 : CNF.NClause := [(84,true),(148,false),(24,false),(2,true)]
theorem der_63651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63651 :=
  CNF.rup_sound cl_63651 [cl_43263,cl_48242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43263 v h) (hints_cons _ _ _ (der_48242 v h) (by intro d hd; cases hd)))
def cl_63662 : CNF.NClause := [(114,true),(57,false),(35,false)]
theorem der_63662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63662 :=
  CNF.rup_sound cl_63662 [cl_49724,cl_50226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49724 v h) (hints_cons _ _ _ (der_50226 v h) (by intro d hd; cases hd)))
def cl_63665 : CNF.NClause := [(1060,false),(66,true)]
theorem der_63665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63665 :=
  CNF.rup_sound cl_63665 [cl_15912,cl_49788,cl_45588,cl_15922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_49788 v h) (hints_cons _ _ _ (der_45588 v h) (hints_cons _ _ _ (der_15922 v h) (by intro d hd; cases hd)))))
def cl_63667 : CNF.NClause := [(43,false),(110,false),(52,true),(42,true),(99,false),(114,false),(57,false),(59,false),(38,true),(40,true),(50,false),(53,false)]
theorem der_63667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63667 :=
  CNF.rup_sound cl_63667 [cl_62561,cl_62559,cl_50051,cl_63458,cl_50381,cl_50219,cl_62391,cl_7949,cl_56213,cl_48629,cl_31931,cl_50333,cl_7963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_50051 v h) (hints_cons _ _ _ (der_63458 v h) (hints_cons _ _ _ (der_50381 v h) (hints_cons _ _ _ (der_50219 v h) (hints_cons _ _ _ (der_62391 v h) (hints_cons _ _ _ (inp_7949 v h) (hints_cons _ _ _ (der_56213 v h) (hints_cons _ _ _ (der_48629 v h) (hints_cons _ _ _ (der_31931 v h) (hints_cons _ _ _ (der_50333 v h) (hints_cons _ _ _ (inp_7963 v h) (by intro d hd; cases hd))))))))))))))
def cl_63674 : CNF.NClause := [(116,true),(43,false),(50,false)]
theorem der_63674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63674 :=
  CNF.rup_sound cl_63674 [cl_50035,cl_62391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50035 v h) (hints_cons _ _ _ (der_62391 v h) (by intro d hd; cases hd)))
def cl_63714 : CNF.NClause := [(84,true),(24,false),(210,true),(2,true)]
theorem der_63714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63714 :=
  CNF.rup_sound cl_63714 [cl_13737,cl_49973,cl_43263,cl_13838,cl_13853,cl_50198,cl_13830,cl_50195,cl_8477,cl_13841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13737 v h) (hints_cons _ _ _ (der_49973 v h) (hints_cons _ _ _ (der_43263 v h) (hints_cons _ _ _ (inp_13838 v h) (hints_cons _ _ _ (inp_13853 v h) (hints_cons _ _ _ (der_50198 v h) (hints_cons _ _ _ (inp_13830 v h) (hints_cons _ _ _ (der_50195 v h) (hints_cons _ _ _ (inp_8477 v h) (hints_cons _ _ _ (inp_13841 v h) (by intro d hd; cases hd)))))))))))
def cl_63743 : CNF.NClause := [(66,true),(150,true),(153,true),(138,true),(142,true),(133,true),(126,true),(139,true),(131,true),(146,false)]
theorem der_63743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63743 :=
  CNF.rup_sound cl_63743 [cl_56933,cl_60437,cl_62573,cl_8113,cl_8074,cl_15660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56933 v h) (hints_cons _ _ _ (der_60437 v h) (hints_cons _ _ _ (der_62573 v h) (hints_cons _ _ _ (inp_8113 v h) (hints_cons _ _ _ (inp_8074 v h) (hints_cons _ _ _ (der_15660 v h) (by intro d hd; cases hd)))))))
def cl_63746 : CNF.NClause := [(73,true),(469,true),(483,false),(18,false),(11,true),(7,true)]
theorem der_63746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63746 :=
  CNF.rup_sound cl_63746 [cl_14103,cl_57860,cl_56327,cl_56258,cl_14123,cl_14116,cl_14106,cl_10082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14103 v h) (hints_cons _ _ _ (der_57860 v h) (hints_cons _ _ _ (der_56327 v h) (hints_cons _ _ _ (der_56258 v h) (hints_cons _ _ _ (inp_14123 v h) (hints_cons _ _ _ (inp_14116 v h) (hints_cons _ _ _ (inp_14106 v h) (hints_cons _ _ _ (inp_10082 v h) (by intro d hd; cases hd)))))))))
def cl_63749 : CNF.NClause := [(81,true),(125,true),(152,false),(133,true),(15,true)]
theorem der_63749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63749 :=
  CNF.rup_sound cl_63749 [cl_15781,cl_61053,cl_63631,cl_8082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_61053 v h) (hints_cons _ _ _ (der_63631 v h) (hints_cons _ _ _ (inp_8082 v h) (by intro d hd; cases hd)))))
def cl_63752 : CNF.NClause := [(79,true),(150,false),(138,true),(126,true)]
theorem der_63752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63752 :=
  CNF.rup_sound cl_63752 [cl_56741,cl_62705,cl_62991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56741 v h) (hints_cons _ _ _ (der_62705 v h) (hints_cons _ _ _ (der_62991 v h) (by intro d hd; cases hd))))
def cl_63753 : CNF.NClause := [(81,true),(152,false),(133,true),(15,true)]
theorem der_63753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63753 :=
  CNF.rup_sound cl_63753 [cl_61806,cl_63749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61806 v h) (hints_cons _ _ _ (der_63749 v h) (by intro d hd; cases hd)))
def cl_63761 : CNF.NClause := [(76,true),(148,false)]
theorem der_63761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63761 :=
  CNF.rup_sound cl_63761 [cl_15790,cl_61991,cl_63645,cl_57751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_61991 v h) (hints_cons _ _ _ (der_63645 v h) (hints_cons _ _ _ (der_57751 v h) (by intro d hd; cases hd)))))
def cl_63771 : CNF.NClause := [(145,true),(137,true),(127,true),(148,true),(150,true),(138,true),(142,true),(144,true),(126,true),(139,true),(146,false)]
theorem der_63771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63771 :=
  CNF.rup_sound cl_63771 [cl_8074,cl_15643,cl_15631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8074 v h) (hints_cons _ _ _ (der_15643 v h) (hints_cons _ _ _ (der_15631 v h) (by intro d hd; cases hd))))
def cl_63775 : CNF.NClause := [(148,false),(84,true),(2,true)]
theorem der_63775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63775 :=
  CNF.rup_sound cl_63775 [cl_15790,cl_63651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_63651 v h) (by intro d hd; cases hd)))
def cl_63793 : CNF.NClause := [(150,false),(57,true),(62,false),(71,false),(83,false),(138,true),(91,false),(126,true),(75,false)]
theorem der_63793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63793 :=
  CNF.rup_sound cl_63793 [cl_15791,cl_63752,cl_7297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_63752 v h) (hints_cons _ _ _ (inp_7297 v h) (by intro d hd; cases hd))))
def cl_63795 : CNF.NClause := [(119,true),(60,false),(48,false)]
theorem der_63795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63795 :=
  CNF.rup_sound cl_63795 [cl_62561,cl_50373,cl_51472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50373 v h) (hints_cons _ _ _ (der_51472 v h) (by intro d hd; cases hd))))
def cl_63802 : CNF.NClause := [(114,true),(57,false),(48,false)]
theorem der_63802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63802 :=
  CNF.rup_sound cl_63802 [cl_50024,cl_49585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50024 v h) (hints_cons _ _ _ (der_49585 v h) (by intro d hd; cases hd)))
def cl_63840 : CNF.NClause := [(71,true),(26,false),(19,false),(7,true)]
theorem der_63840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63840 :=
  CNF.rup_sound cl_63840 [cl_50118,cl_49564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50118 v h) (hints_cons _ _ _ (der_49564 v h) (by intro d hd; cases hd)))
def cl_63850 : CNF.NClause := [(48,false),(99,false),(60,false),(94,false),(55,false),(122,false),(50,false),(57,false),(95,false),(58,true),(53,false)]
theorem der_63850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63850 :=
  CNF.rup_sound cl_63850 [cl_62559,cl_50040,cl_61711,cl_50366,cl_48917,cl_48712,cl_63802,cl_63795,cl_7954,cl_7961,cl_49845,cl_49852,cl_50316,cl_50384,cl_7966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_50040 v h) (hints_cons _ _ _ (der_61711 v h) (hints_cons _ _ _ (der_50366 v h) (hints_cons _ _ _ (der_48917 v h) (hints_cons _ _ _ (der_48712 v h) (hints_cons _ _ _ (der_63802 v h) (hints_cons _ _ _ (der_63795 v h) (hints_cons _ _ _ (inp_7954 v h) (hints_cons _ _ _ (inp_7961 v h) (hints_cons _ _ _ (der_49845 v h) (hints_cons _ _ _ (der_49852 v h) (hints_cons _ _ _ (der_50316 v h) (hints_cons _ _ _ (der_50384 v h) (hints_cons _ _ _ (inp_7966 v h) (by intro d hd; cases hd))))))))))))))))
def cl_63872 : CNF.NClause := [(85,true),(763,false),(19,false),(27,true),(20,true)]
theorem der_63872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63872 :=
  CNF.rup_sound cl_63872 [cl_14392,cl_54411,cl_54039,cl_49887,cl_53710,cl_14386,cl_14369,cl_14371,cl_11828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14392 v h) (hints_cons _ _ _ (der_54411 v h) (hints_cons _ _ _ (der_54039 v h) (hints_cons _ _ _ (der_49887 v h) (hints_cons _ _ _ (der_53710 v h) (hints_cons _ _ _ (inp_14386 v h) (hints_cons _ _ _ (inp_14369 v h) (hints_cons _ _ _ (inp_14371 v h) (hints_cons _ _ _ (inp_11828 v h) (by intro d hd; cases hd))))))))))
def cl_63882 : CNF.NClause := [(48,false),(52,false),(50,false),(58,true),(114,false),(32,false),(59,false),(53,false)]
theorem der_63882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63882 :=
  CNF.rup_sound cl_63882 [cl_62559,cl_62561,cl_55115,cl_62370,cl_48917,cl_49471,cl_49584,cl_7954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_55115 v h) (hints_cons _ _ _ (der_62370 v h) (hints_cons _ _ _ (der_48917 v h) (hints_cons _ _ _ (der_49471 v h) (hints_cons _ _ _ (der_49584 v h) (hints_cons _ _ _ (inp_7954 v h) (by intro d hd; cases hd)))))))))
def cl_63895 : CNF.NClause := [(88,true),(152,true),(128,true),(29,false),(138,true),(142,true),(126,true),(135,true),(131,true),(146,false)]
theorem der_63895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63895 :=
  CNF.rup_sound cl_63895 [cl_49908,cl_50458,cl_49836,cl_15783,cl_15779,cl_15787,cl_15626,cl_8037,cl_15648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49908 v h) (hints_cons _ _ _ (der_50458 v h) (hints_cons _ _ _ (der_49836 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15626 v h) (hints_cons _ _ _ (inp_8037 v h) (hints_cons _ _ _ (der_15648 v h) (by intro d hd; cases hd))))))))))
def cl_63921 : CNF.NClause := [(71,true),(918,false),(19,false),(919,true),(7,true)]
theorem der_63921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63921 :=
  CNF.rup_sound cl_63921 [cl_15873,cl_50118,cl_39541,cl_63840,cl_15879,cl_15867,cl_15891,cl_12674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15873 v h) (hints_cons _ _ _ (der_50118 v h) (hints_cons _ _ _ (der_39541 v h) (hints_cons _ _ _ (der_63840 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (inp_12674 v h) (by intro d hd; cases hd)))))))))
def cl_63928 : CNF.NClause := [(145,false),(52,true),(88,false),(85,false),(128,true),(135,true),(7,true),(67,false)]
theorem der_63928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63928 :=
  CNF.rup_sound cl_63928 [cl_56741,cl_57043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56741 v h) (hints_cons _ _ _ (der_57043 v h) (by intro d hd; cases hd)))
def cl_63950 : CNF.NClause := [(68,true),(4,true),(143,true),(20,true),(142,true),(126,true),(139,true),(131,true),(146,false)]
theorem der_63950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63950 :=
  CNF.rup_sound cl_63950 [cl_15770,cl_49402,cl_57257,cl_15653,cl_15626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_49402 v h) (hints_cons _ _ _ (der_57257 v h) (hints_cons _ _ _ (der_15653 v h) (hints_cons _ _ _ (der_15626 v h) (by intro d hd; cases hd))))))
def cl_63952 : CNF.NClause := [(141,false),(76,true),(151,true)]
theorem der_63952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63952 :=
  CNF.rup_sound cl_63952 [cl_63761,cl_54207,cl_61991,cl_15783,cl_8054,cl_53690,cl_15774,cl_52032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63761 v h) (hints_cons _ _ _ (der_54207 v h) (hints_cons _ _ _ (der_61991 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (inp_8054 v h) (hints_cons _ _ _ (der_53690 v h) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_52032 v h) (by intro d hd; cases hd)))))))))
def cl_63957 : CNF.NClause := [(128,false),(23,true),(83,true),(11,true)]
theorem der_63957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63957 :=
  CNF.rup_sound cl_63957 [cl_15770,cl_50523,cl_62690,cl_60488,cl_30603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_50523 v h) (hints_cons _ _ _ (der_62690 v h) (hints_cons _ _ _ (der_60488 v h) (hints_cons _ _ _ (der_30603 v h) (by intro d hd; cases hd))))))
def cl_63960 : CNF.NClause := [(73,true),(483,false),(18,false),(11,true),(7,true)]
theorem der_63960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63960 :=
  CNF.rup_sound cl_63960 [cl_50398,cl_63746,cl_14100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50398 v h) (hints_cons _ _ _ (der_63746 v h) (hints_cons _ _ _ (inp_14100 v h) (by intro d hd; cases hd))))
def cl_63963 : CNF.NClause := [(128,false),(83,true),(11,true)]
theorem der_63963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63963 :=
  CNF.rup_sound cl_63963 [cl_15770,cl_63957,cl_63594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_63957 v h) (hints_cons _ _ _ (der_63594 v h) (by intro d hd; cases hd))))
def cl_63986 : CNF.NClause := [(129,false),(85,true)]
theorem der_63986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_63986 :=
  CNF.rup_sound cl_63986 [cl_62591,cl_15771,cl_53763,cl_60483,cl_50160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62591 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_53763 v h) (hints_cons _ _ _ (der_60483 v h) (hints_cons _ _ _ (der_50160 v h) (by intro d hd; cases hd))))))
def cl_64006 : CNF.NClause := [(60,true),(246,false),(29,false),(3,true),(80,false),(68,false),(88,false),(74,false),(86,false)]
theorem der_64006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64006 :=
  CNF.rup_sound cl_64006 [cl_49488,cl_36836,cl_13883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49488 v h) (hints_cons _ _ _ (der_36836 v h) (hints_cons _ _ _ (inp_13883 v h) (by intro d hd; cases hd))))
def cl_64012 : CNF.NClause := [(85,true),(137,false),(127,true),(152,true),(128,true),(143,true),(138,true),(142,true),(151,true),(135,true),(131,true)]
theorem der_64012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64012 :=
  CNF.rup_sound cl_64012 [cl_62572,cl_63986,cl_15647,cl_8107,cl_8037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62572 v h) (hints_cons _ _ _ (der_63986 v h) (hints_cons _ _ _ (der_15647 v h) (hints_cons _ _ _ (inp_8107 v h) (hints_cons _ _ _ (inp_8037 v h) (by intro d hd; cases hd))))))
def cl_64022 : CNF.NClause := [(110,true),(52,false),(57,false)]
theorem der_64022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64022 :=
  CNF.rup_sound cl_64022 [cl_54743,cl_50321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54743 v h) (hints_cons _ _ _ (der_50321 v h) (by intro d hd; cases hd)))
def cl_64028 : CNF.NClause := [(911,false),(1,true),(81,true),(908,true),(15,true)]
theorem der_64028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64028 :=
  CNF.rup_sound cl_64028 [cl_15867,cl_15881,cl_15878,cl_50136,cl_51540,cl_15893,cl_15889,cl_12735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_50136 v h) (hints_cons _ _ _ (der_51540 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (inp_12735 v h) (by intro d hd; cases hd)))))))))
def cl_64034 : CNF.NClause := [(37,false),(110,false),(106,false),(93,false),(114,false),(57,false),(44,false),(71,false),(66,false),(70,false),(73,false),(7,true),(64,false),(78,false)]
theorem der_64034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64034 :=
  CNF.rup_sound cl_64034 [cl_62561,cl_50662,cl_50306,cl_33475,cl_7963,cl_50375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50662 v h) (hints_cons _ _ _ (der_50306 v h) (hints_cons _ _ _ (der_33475 v h) (hints_cons _ _ _ (inp_7963 v h) (hints_cons _ _ _ (der_50375 v h) (by intro d hd; cases hd)))))))
def cl_64042 : CNF.NClause := [(102,true),(57,false),(44,false),(50,true)]
theorem der_64042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64042 :=
  CNF.rup_sound cl_64042 [cl_50378,cl_50375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50378 v h) (hints_cons _ _ _ (der_50375 v h) (by intro d hd; cases hd)))
def cl_64050 : CNF.NClause := [(66,true),(141,true),(152,true),(128,true),(138,true),(69,true)]
theorem der_64050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64050 :=
  CNF.rup_sound cl_64050 [cl_56888,cl_56868,cl_56933,cl_62573,cl_15661,cl_8021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56888 v h) (hints_cons _ _ _ (der_56868 v h) (hints_cons _ _ _ (der_56933 v h) (hints_cons _ _ _ (der_62573 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (inp_8021 v h) (by intro d hd; cases hd)))))))
def cl_64053 : CNF.NClause := [(150,false),(71,true),(143,true),(144,true),(7,true)]
theorem der_64053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64053 :=
  CNF.rup_sound cl_64053 [cl_15773,cl_15791,cl_61646,cl_50120,cl_15767,cl_15779,cl_8022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_61646 v h) (hints_cons _ _ _ (der_50120 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (inp_8022 v h) (by intro d hd; cases hd))))))))
def cl_64065 : CNF.NClause := [(102,true),(32,false),(57,false),(50,true)]
theorem der_64065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64065 :=
  CNF.rup_sound cl_64065 [cl_64042,cl_31934,cl_51502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64042 v h) (hints_cons _ _ _ (der_31934 v h) (hints_cons _ _ _ (der_51502 v h) (by intro d hd; cases hd))))
def cl_64072 : CNF.NClause := [(130,false),(37,true),(66,false),(70,false),(74,false),(18,false),(78,false)]
theorem der_64072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64072 :=
  CNF.rup_sound cl_64072 [cl_15772,cl_57205,cl_53892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_57205 v h) (hints_cons _ _ _ (der_53892 v h) (by intro d hd; cases hd))))
def cl_64082 : CNF.NClause := [(68,true),(143,true),(146,false),(20,true),(142,true),(126,true),(139,true),(131,true)]
theorem der_64082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64082 :=
  CNF.rup_sound cl_64082 [cl_63950,cl_49530,cl_49989,cl_63563,cl_15778,cl_15653,cl_15626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63950 v h) (hints_cons _ _ _ (der_49530 v h) (hints_cons _ _ _ (der_49989 v h) (hints_cons _ _ _ (der_63563 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_15653 v h) (hints_cons _ _ _ (der_15626 v h) (by intro d hd; cases hd))))))))
def cl_64097 : CNF.NClause := [(120,true),(58,false),(38,false),(54,true)]
theorem der_64097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64097 :=
  CNF.rup_sound cl_64097 [cl_62561,cl_50814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50814 v h) (by intro d hd; cases hd)))
def cl_64098 : CNF.NClause := [(120,true),(58,false),(47,true),(38,false)]
theorem der_64098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64098 :=
  CNF.rup_sound cl_64098 [cl_62561,cl_50815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50815 v h) (by intro d hd; cases hd)))
def cl_64103 : CNF.NClause := [(120,true),(45,false),(38,true),(54,false)]
theorem der_64103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64103 :=
  CNF.rup_sound cl_64103 [cl_62561,cl_50820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50820 v h) (by intro d hd; cases hd)))
def cl_64104 : CNF.NClause := [(120,false),(47,true),(38,true),(45,true),(58,true)]
theorem der_64104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64104 :=
  CNF.rup_sound cl_64104 [cl_62561,cl_32636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_32636 v h) (by intro d hd; cases hd)))
def cl_64105 : CNF.NClause := [(120,true),(45,false),(47,false),(38,true)]
theorem der_64105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64105 :=
  CNF.rup_sound cl_64105 [cl_62561,cl_50821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50821 v h) (by intro d hd; cases hd)))
def cl_64106 : CNF.NClause := [(120,false),(45,true),(58,true),(38,true),(54,true)]
theorem der_64106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64106 :=
  CNF.rup_sound cl_64106 [cl_62561,cl_32637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_32637 v h) (by intro d hd; cases hd)))
def cl_64107 : CNF.NClause := [(120,false),(47,true),(38,true),(54,true),(58,true)]
theorem der_64107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64107 :=
  CNF.rup_sound cl_64107 [cl_62561,cl_32638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_32638 v h) (by intro d hd; cases hd)))
def cl_64108 : CNF.NClause := [(120,false),(45,true),(47,true),(58,true),(54,true)]
theorem der_64108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64108 :=
  CNF.rup_sound cl_64108 [cl_62561,cl_32639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_32639 v h) (by intro d hd; cases hd)))
def cl_64109 : CNF.NClause := [(120,false),(47,true),(45,true),(38,true),(54,true)]
theorem der_64109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64109 :=
  CNF.rup_sound cl_64109 [cl_62561,cl_23712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23712 v h) (by intro d hd; cases hd)))
def cl_64111 : CNF.NClause := [(50,false),(121,true),(59,false),(53,true)]
theorem der_64111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64111 :=
  CNF.rup_sound cl_64111 [cl_62561,cl_50998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50998 v h) (by intro d hd; cases hd)))
def cl_64113 : CNF.NClause := [(59,true),(39,true),(121,false),(53,true),(42,true)]
theorem der_64113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64113 :=
  CNF.rup_sound cl_64113 [cl_62561,cl_33148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_33148 v h) (by intro d hd; cases hd)))
def cl_64115 : CNF.NClause := [(42,false),(121,true),(59,false)]
theorem der_64115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64115 :=
  CNF.rup_sound cl_64115 [cl_62561,cl_50088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50088 v h) (by intro d hd; cases hd)))
def cl_64116 : CNF.NClause := [(42,false),(121,true),(39,false)]
theorem der_64116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64116 :=
  CNF.rup_sound cl_64116 [cl_62561,cl_50089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50089 v h) (by intro d hd; cases hd)))
def cl_64117 : CNF.NClause := [(59,true),(39,true),(50,true),(121,false),(53,true)]
theorem der_64117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64117 :=
  CNF.rup_sound cl_64117 [cl_62561,cl_33149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_33149 v h) (by intro d hd; cases hd)))
def cl_64118 : CNF.NClause := [(108,true),(49,false),(47,true),(50,false)]
theorem der_64118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64118 :=
  CNF.rup_sound cl_64118 [cl_62559,cl_51030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_51030 v h) (by intro d hd; cases hd)))
def cl_64120 : CNF.NClause := [(108,false),(47,true),(46,true),(50,true),(49,true)]
theorem der_64120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64120 :=
  CNF.rup_sound cl_64120 [cl_62559,cl_33243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_33243 v h) (by intro d hd; cases hd)))
def cl_64121 : CNF.NClause := [(119,true),(52,false),(48,false),(60,true)]
theorem der_64121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64121 :=
  CNF.rup_sound cl_64121 [cl_62561,cl_51032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51032 v h) (by intro d hd; cases hd)))
def cl_64122 : CNF.NClause := [(119,false),(52,true),(60,true),(44,true),(40,true)]
theorem der_64122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64122 :=
  CNF.rup_sound cl_64122 [cl_62561,cl_33245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_33245 v h) (by intro d hd; cases hd)))
def cl_64123 : CNF.NClause := [(119,false),(52,true),(48,true),(44,true),(40,true)]
theorem der_64123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64123 :=
  CNF.rup_sound cl_64123 [cl_62561,cl_23802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23802 v h) (by intro d hd; cases hd)))
def cl_64125 : CNF.NClause := [(55,true),(37,true),(122,false),(49,true),(57,true)]
theorem der_64125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64125 :=
  CNF.rup_sound cl_64125 [cl_62561,cl_33608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_33608 v h) (by intro d hd; cases hd)))
def cl_64126 : CNF.NClause := [(55,true),(43,true),(122,false),(49,true),(57,true)]
theorem der_64126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64126 :=
  CNF.rup_sound cl_64126 [cl_62561,cl_33609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_33609 v h) (by intro d hd; cases hd)))
def cl_64127 : CNF.NClause := [(122,false),(37,true),(49,true),(43,true),(55,true)]
theorem der_64127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64127 :=
  CNF.rup_sound cl_64127 [cl_62561,cl_23811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23811 v h) (by intro d hd; cases hd)))
def cl_64130 : CNF.NClause := [(108,false),(47,true),(46,true),(48,true),(49,true)]
theorem der_64130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64130 :=
  CNF.rup_sound cl_64130 [cl_62559,cl_23854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_23854 v h) (by intro d hd; cases hd)))
def cl_64131 : CNF.NClause := [(108,true),(46,false),(49,false)]
theorem der_64131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64131 :=
  CNF.rup_sound cl_64131 [cl_62559,cl_36297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_36297 v h) (by intro d hd; cases hd)))
def cl_64132 : CNF.NClause := [(119,false),(52,true),(60,true),(44,true),(48,true)]
theorem der_64132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64132 :=
  CNF.rup_sound cl_64132 [cl_62561,cl_23863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23863 v h) (by intro d hd; cases hd)))
def cl_64134 : CNF.NClause := [(119,true),(48,false),(44,true),(60,false)]
theorem der_64134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64134 :=
  CNF.rup_sound cl_64134 [cl_62561,cl_51472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51472 v h) (by intro d hd; cases hd)))
def cl_64135 : CNF.NClause := [(119,true),(40,false),(52,false)]
theorem der_64135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64135 :=
  CNF.rup_sound cl_64135 [cl_62561,cl_50091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50091 v h) (by intro d hd; cases hd)))
def cl_64136 : CNF.NClause := [(123,false),(36,true),(46,true),(41,true)]
theorem der_64136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64136 :=
  CNF.rup_sound cl_64136 [cl_62561,cl_54880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54880 v h) (by intro d hd; cases hd)))
def cl_64137 : CNF.NClause := [(123,false),(36,true),(41,true),(51,true)]
theorem der_64137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64137 :=
  CNF.rup_sound cl_64137 [cl_62561,cl_54881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54881 v h) (by intro d hd; cases hd)))
def cl_64138 : CNF.NClause := [(123,false),(36,true),(51,true),(46,true)]
theorem der_64138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64138 :=
  CNF.rup_sound cl_64138 [cl_62561,cl_54882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54882 v h) (by intro d hd; cases hd)))
def cl_64139 : CNF.NClause := [(123,false),(41,true),(46,true),(51,true)]
theorem der_64139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64139 :=
  CNF.rup_sound cl_64139 [cl_62561,cl_54883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54883 v h) (by intro d hd; cases hd)))
def cl_64141 : CNF.NClause := [(113,false),(36,true),(37,true),(38,true),(39,true)]
theorem der_64141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64141 :=
  CNF.rup_sound cl_64141 [cl_62559,cl_34185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34185 v h) (by intro d hd; cases hd)))
def cl_64142 : CNF.NClause := [(113,false),(37,true),(38,true),(36,true),(40,true)]
theorem der_64142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64142 :=
  CNF.rup_sound cl_64142 [cl_62559,cl_34186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34186 v h) (by intro d hd; cases hd)))
def cl_64143 : CNF.NClause := [(113,false),(36,true),(39,true),(37,true),(40,true)]
theorem der_64143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64143 :=
  CNF.rup_sound cl_64143 [cl_62559,cl_34187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34187 v h) (by intro d hd; cases hd)))
def cl_64144 : CNF.NClause := [(113,false),(36,true),(40,true),(39,true),(38,true)]
theorem der_64144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64144 :=
  CNF.rup_sound cl_64144 [cl_62559,cl_34188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34188 v h) (by intro d hd; cases hd)))
def cl_64145 : CNF.NClause := [(113,false),(39,true),(38,true),(40,true),(37,true)]
theorem der_64145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64145 :=
  CNF.rup_sound cl_64145 [cl_62559,cl_34189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34189 v h) (by intro d hd; cases hd)))
def cl_64146 : CNF.NClause := [(122,false),(37,true),(49,true),(57,true),(43,true)]
theorem der_64146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64146 :=
  CNF.rup_sound cl_64146 [cl_62561,cl_23928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23928 v h) (by intro d hd; cases hd)))
def cl_64147 : CNF.NClause := [(55,true),(43,true),(37,true),(57,true),(122,false)]
theorem der_64147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64147 :=
  CNF.rup_sound cl_64147 [cl_62561,cl_23929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23929 v h) (by intro d hd; cases hd)))
def cl_64148 : CNF.NClause := [(103,false),(41,true),(44,true),(42,true),(43,true)]
theorem der_64148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64148 :=
  CNF.rup_sound cl_64148 [cl_62559,cl_34206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34206 v h) (by intro d hd; cases hd)))
def cl_64149 : CNF.NClause := [(103,false),(45,true),(42,true),(43,true),(41,true)]
theorem der_64149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64149 :=
  CNF.rup_sound cl_64149 [cl_62559,cl_34207] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34207 v h) (by intro d hd; cases hd)))
def cl_64150 : CNF.NClause := [(103,false),(45,true),(42,true),(41,true),(44,true)]
theorem der_64150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64150 :=
  CNF.rup_sound cl_64150 [cl_62559,cl_34208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34208 v h) (by intro d hd; cases hd)))
def cl_64151 : CNF.NClause := [(103,false),(41,true),(44,true),(45,true),(43,true)]
theorem der_64151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64151 :=
  CNF.rup_sound cl_64151 [cl_62559,cl_34209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34209 v h) (by intro d hd; cases hd)))
def cl_64152 : CNF.NClause := [(103,false),(45,true),(43,true),(44,true),(42,true)]
theorem der_64152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64152 :=
  CNF.rup_sound cl_64152 [cl_62559,cl_23931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_23931 v h) (by intro d hd; cases hd)))
def cl_64153 : CNF.NClause := [(108,false),(47,true),(48,true),(50,true),(46,true)]
theorem der_64153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64153 :=
  CNF.rup_sound cl_64153 [cl_62559,cl_23933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_23933 v h) (by intro d hd; cases hd)))
def cl_64154 : CNF.NClause := [(108,false),(46,true),(49,true),(50,true),(48,true)]
theorem der_64154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64154 :=
  CNF.rup_sound cl_64154 [cl_62559,cl_23934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_23934 v h) (by intro d hd; cases hd)))
def cl_64155 : CNF.NClause := [(108,false),(47,true),(49,true),(50,true),(48,true)]
theorem der_64155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64155 :=
  CNF.rup_sound cl_64155 [cl_62559,cl_23935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_23935 v h) (by intro d hd; cases hd)))
def cl_64156 : CNF.NClause := [(118,false),(32,true),(33,true),(34,true)]
theorem der_64156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64156 :=
  CNF.rup_sound cl_64156 [cl_62561,cl_62559,cl_34237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34237 v h) (by intro d hd; cases hd))))
def cl_64157 : CNF.NClause := [(118,false),(32,true),(33,true),(35,true)]
theorem der_64157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64157 :=
  CNF.rup_sound cl_64157 [cl_62561,cl_62559,cl_34238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34238 v h) (by intro d hd; cases hd))))
def cl_64158 : CNF.NClause := [(118,false),(35,true),(32,true),(34,true)]
theorem der_64158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64158 :=
  CNF.rup_sound cl_64158 [cl_62561,cl_62559,cl_34239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34239 v h) (by intro d hd; cases hd))))
def cl_64159 : CNF.NClause := [(118,false),(35,true),(33,true),(34,true)]
theorem der_64159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64159 :=
  CNF.rup_sound cl_64159 [cl_62559,cl_62561,cl_34240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_34240 v h) (by intro d hd; cases hd))))
def cl_64162 : CNF.NClause := [(50,true),(121,false),(42,true),(53,true),(39,true)]
theorem der_64162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64162 :=
  CNF.rup_sound cl_64162 [cl_62561,cl_23946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23946 v h) (by intro d hd; cases hd)))
def cl_64163 : CNF.NClause := [(121,false),(39,true),(59,true),(42,true),(50,true)]
theorem der_64163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64163 :=
  CNF.rup_sound cl_64163 [cl_62561,cl_23947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23947 v h) (by intro d hd; cases hd)))
def cl_64164 : CNF.NClause := [(121,false),(59,true),(42,true),(50,true),(53,true)]
theorem der_64164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64164 :=
  CNF.rup_sound cl_64164 [cl_62561,cl_23948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23948 v h) (by intro d hd; cases hd)))
def cl_64165 : CNF.NClause := [(98,false),(52,true),(54,true),(51,true),(53,true)]
theorem der_64165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64165 :=
  CNF.rup_sound cl_64165 [cl_62559,cl_34248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34248 v h) (by intro d hd; cases hd)))
def cl_64166 : CNF.NClause := [(98,false),(55,true),(51,true),(53,true),(52,true)]
theorem der_64166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64166 :=
  CNF.rup_sound cl_64166 [cl_62559,cl_34249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34249 v h) (by intro d hd; cases hd)))
def cl_64167 : CNF.NClause := [(98,false),(54,true),(55,true),(51,true),(52,true)]
theorem der_64167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64167 :=
  CNF.rup_sound cl_64167 [cl_62559,cl_34250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34250 v h) (by intro d hd; cases hd)))
def cl_64168 : CNF.NClause := [(98,false),(54,true),(55,true),(51,true),(53,true)]
theorem der_64168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64168 :=
  CNF.rup_sound cl_64168 [cl_62559,cl_34251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_34251 v h) (by intro d hd; cases hd)))
def cl_64169 : CNF.NClause := [(98,false),(52,true),(53,true),(54,true),(55,true)]
theorem der_64169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64169 :=
  CNF.rup_sound cl_64169 [cl_62559,cl_23950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_23950 v h) (by intro d hd; cases hd)))
def cl_64170 : CNF.NClause := [(93,false),(57,true),(59,true),(58,true)]
theorem der_64170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64170 :=
  CNF.rup_sound cl_64170 [cl_62559,cl_54900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_54900 v h) (by intro d hd; cases hd)))
def cl_64171 : CNF.NClause := [(93,false),(57,true),(60,true),(58,true)]
theorem der_64171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64171 :=
  CNF.rup_sound cl_64171 [cl_62559,cl_54901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_54901 v h) (by intro d hd; cases hd)))
def cl_64172 : CNF.NClause := [(93,false),(57,true),(60,true),(59,true)]
theorem der_64172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64172 :=
  CNF.rup_sound cl_64172 [cl_62559,cl_54902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_54902 v h) (by intro d hd; cases hd)))
def cl_64173 : CNF.NClause := [(93,false),(60,true),(59,true),(58,true)]
theorem der_64173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64173 :=
  CNF.rup_sound cl_64173 [cl_62559,cl_54903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_54903 v h) (by intro d hd; cases hd)))
def cl_64175 : CNF.NClause := [(119,false),(44,true),(40,true),(60,true),(48,true)]
theorem der_64175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64175 :=
  CNF.rup_sound cl_64175 [cl_62561,cl_23958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23958 v h) (by intro d hd; cases hd)))
def cl_64176 : CNF.NClause := [(119,false),(52,true),(40,true),(60,true),(48,true)]
theorem der_64176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64176 :=
  CNF.rup_sound cl_64176 [cl_62561,cl_23959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_23959 v h) (by intro d hd; cases hd)))
def cl_64178 : CNF.NClause := [(121,true),(42,true),(59,false),(53,false)]
theorem der_64178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64178 :=
  CNF.rup_sound cl_64178 [cl_62561,cl_51737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51737 v h) (by intro d hd; cases hd)))
def cl_64179 : CNF.NClause := [(113,true),(40,false),(39,true),(36,false)]
theorem der_64179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64179 :=
  CNF.rup_sound cl_64179 [cl_62559,cl_30808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_30808 v h) (by intro d hd; cases hd)))
def cl_64180 : CNF.NClause := [(113,true),(36,false),(40,true),(39,false)]
theorem der_64180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64180 :=
  CNF.rup_sound cl_64180 [cl_62559,cl_44349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_44349 v h) (by intro d hd; cases hd)))
def cl_64182 : CNF.NClause := [(122,true),(57,false),(55,false),(37,true)]
theorem der_64182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64182 :=
  CNF.rup_sound cl_64182 [cl_62561,cl_51743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51743 v h) (by intro d hd; cases hd)))
def cl_64183 : CNF.NClause := [(49,false),(122,true),(55,true),(43,false)]
theorem der_64183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64183 :=
  CNF.rup_sound cl_64183 [cl_62561,cl_51744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51744 v h) (by intro d hd; cases hd)))
def cl_64184 : CNF.NClause := [(122,true),(49,false),(43,true),(57,false)]
theorem der_64184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64184 :=
  CNF.rup_sound cl_64184 [cl_62561,cl_51745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51745 v h) (by intro d hd; cases hd)))
def cl_64185 : CNF.NClause := [(122,true),(57,false),(43,false)]
theorem der_64185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64185 :=
  CNF.rup_sound cl_64185 [cl_62561,cl_50219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50219 v h) (by intro d hd; cases hd)))
def cl_64186 : CNF.NClause := [(49,false),(122,true),(55,false),(43,true)]
theorem der_64186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64186 :=
  CNF.rup_sound cl_64186 [cl_62561,cl_51746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51746 v h) (by intro d hd; cases hd)))
def cl_64187 : CNF.NClause := [(122,true),(55,false),(43,false)]
theorem der_64187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64187 :=
  CNF.rup_sound cl_64187 [cl_62561,cl_50220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50220 v h) (by intro d hd; cases hd)))
def cl_64190 : CNF.NClause := [(113,true),(40,false),(39,false)]
theorem der_64190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64190 :=
  CNF.rup_sound cl_64190 [cl_62559,cl_56265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_56265 v h) (by intro d hd; cases hd)))
def cl_64191 : CNF.NClause := [(113,true),(36,true),(37,false),(39,false)]
theorem der_64191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64191 :=
  CNF.rup_sound cl_64191 [cl_62559,cl_30835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_30835 v h) (by intro d hd; cases hd)))
def cl_64192 : CNF.NClause := [(123,true),(51,false),(36,true),(46,false)]
theorem der_64192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64192 :=
  CNF.rup_sound cl_64192 [cl_62561,cl_54913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54913 v h) (by intro d hd; cases hd)))
def cl_64195 : CNF.NClause := [(98,true),(55,false),(51,false)]
theorem der_64195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64195 :=
  CNF.rup_sound cl_64195 [cl_62559,cl_50230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_50230 v h) (by intro d hd; cases hd)))
def cl_64196 : CNF.NClause := [(98,true),(51,false),(53,false)]
theorem der_64196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64196 :=
  CNF.rup_sound cl_64196 [cl_62559,cl_50231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_50231 v h) (by intro d hd; cases hd)))
def cl_64197 : CNF.NClause := [(120,true),(38,false),(45,false),(47,true)]
theorem der_64197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64197 :=
  CNF.rup_sound cl_64197 [cl_62561,cl_51910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51910 v h) (by intro d hd; cases hd)))
def cl_64198 : CNF.NClause := [(120,true),(38,false),(54,false)]
theorem der_64198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64198 :=
  CNF.rup_sound cl_64198 [cl_62561,cl_50233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50233 v h) (by intro d hd; cases hd)))
def cl_64199 : CNF.NClause := [(120,true),(47,false),(54,false)]
theorem der_64199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64199 :=
  CNF.rup_sound cl_64199 [cl_62561,cl_44945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_44945 v h) (by intro d hd; cases hd)))
def cl_64202 : CNF.NClause := [(123,true),(51,false),(41,false)]
theorem der_64202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64202 :=
  CNF.rup_sound cl_64202 [cl_62561,cl_54925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54925 v h) (by intro d hd; cases hd)))
def cl_64204 : CNF.NClause := [(121,true),(39,false),(59,false)]
theorem der_64204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64204 :=
  CNF.rup_sound cl_64204 [cl_62561,cl_43976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_43976 v h) (by intro d hd; cases hd)))
def cl_64205 : CNF.NClause := [(121,true),(39,false),(50,false)]
theorem der_64205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64205 :=
  CNF.rup_sound cl_64205 [cl_62561,cl_50269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50269 v h) (by intro d hd; cases hd)))
def cl_64206 : CNF.NClause := [(123,true),(51,false),(46,false)]
theorem der_64206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64206 :=
  CNF.rup_sound cl_64206 [cl_62561,cl_50299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50299 v h) (by intro d hd; cases hd)))
def cl_64207 : CNF.NClause := [(108,true),(46,false),(48,true),(47,false)]
theorem der_64207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64207 :=
  CNF.rup_sound cl_64207 [cl_62559,cl_51970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_51970 v h) (by intro d hd; cases hd)))
def cl_64209 : CNF.NClause := [(122,true),(57,false),(37,false)]
theorem der_64209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64209 :=
  CNF.rup_sound cl_64209 [cl_62561,cl_50306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50306 v h) (by intro d hd; cases hd)))
def cl_64210 : CNF.NClause := [(121,true),(50,false),(42,true),(53,false)]
theorem der_64210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64210 :=
  CNF.rup_sound cl_64210 [cl_62561,cl_51982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_51982 v h) (by intro d hd; cases hd)))
def cl_64213 : CNF.NClause := [(103,true),(44,false),(43,false)]
theorem der_64213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64213 :=
  CNF.rup_sound cl_64213 [cl_62559,cl_56213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_56213 v h) (by intro d hd; cases hd)))
def cl_64214 : CNF.NClause := [(123,true),(51,false),(36,false)]
theorem der_64214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64214 :=
  CNF.rup_sound cl_64214 [cl_62561,cl_54937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54937 v h) (by intro d hd; cases hd)))
def cl_64215 : CNF.NClause := [(118,true),(33,false),(32,false)]
theorem der_64215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64215 :=
  CNF.rup_sound cl_64215 [cl_62561,cl_62559,cl_52001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_52001 v h) (by intro d hd; cases hd))))
def cl_64216 : CNF.NClause := [(55,false),(98,true),(53,false)]
theorem der_64216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64216 :=
  CNF.rup_sound cl_64216 [cl_62559,cl_50366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_50366 v h) (by intro d hd; cases hd)))
def cl_64217 : CNF.NClause := [(98,true),(52,false),(53,false)]
theorem der_64217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64217 :=
  CNF.rup_sound cl_64217 [cl_62559,cl_50369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_50369 v h) (by intro d hd; cases hd)))
def cl_64219 : CNF.NClause := [(108,true),(46,false),(48,false)]
theorem der_64219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64219 :=
  CNF.rup_sound cl_64219 [cl_62559,cl_42543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_42543 v h) (by intro d hd; cases hd)))
def cl_64220 : CNF.NClause := [(108,true),(46,false),(47,false),(50,true)]
theorem der_64220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64220 :=
  CNF.rup_sound cl_64220 [cl_62559,cl_52004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_52004 v h) (by intro d hd; cases hd)))
def cl_64221 : CNF.NClause := [(119,true),(48,false),(44,false)]
theorem der_64221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64221 :=
  CNF.rup_sound cl_64221 [cl_62561,cl_50373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50373 v h) (by intro d hd; cases hd)))
def cl_64223 : CNF.NClause := [(119,true),(40,false),(48,false)]
theorem der_64223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64223 :=
  CNF.rup_sound cl_64223 [cl_62561,cl_50374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50374 v h) (by intro d hd; cases hd)))
def cl_64224 : CNF.NClause := [(118,true),(34,false),(35,false),(33,true)]
theorem der_64224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64224 :=
  CNF.rup_sound cl_64224 [cl_62559,cl_32020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_32020 v h) (by intro d hd; cases hd)))
def cl_64225 : CNF.NClause := [(118,true),(33,false),(34,false)]
theorem der_64225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64225 :=
  CNF.rup_sound cl_64225 [cl_62561,cl_62559,cl_32021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_32021 v h) (by intro d hd; cases hd))))
def cl_64227 : CNF.NClause := [(113,true),(36,false),(40,true),(39,false),(38,true)]
theorem der_64227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64227 :=
  CNF.rup_sound cl_64227 [cl_62559,cl_35380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_35380 v h) (by intro d hd; cases hd)))
def cl_64229 : CNF.NClause := [(108,true),(47,false),(48,false)]
theorem der_64229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64229 :=
  CNF.rup_sound cl_64229 [cl_62559,cl_35585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_35585 v h) (by intro d hd; cases hd)))
def cl_64233 : CNF.NClause := [(119,true),(44,false),(52,false)]
theorem der_64233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64233 :=
  CNF.rup_sound cl_64233 [cl_62561,cl_50408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50408 v h) (by intro d hd; cases hd)))
def cl_64235 : CNF.NClause := [(123,true),(46,false),(36,false)]
theorem der_64235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64235 :=
  CNF.rup_sound cl_64235 [cl_62561,cl_54957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54957 v h) (by intro d hd; cases hd)))
def cl_64258 : CNF.NClause := [(46,false),(41,false),(47,false),(35,false),(38,true),(115,false),(43,true),(42,false),(45,false),(39,true),(49,true),(53,true),(40,true)]
theorem der_64258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64258 :=
  CNF.rup_sound cl_64258 [cl_62559,cl_62561,cl_55053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_55053 v h) (by intro d hd; cases hd))))
def cl_64261 : CNF.NClause := [(118,true),(33,false),(35,false)]
theorem der_64261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64261 :=
  CNF.rup_sound cl_64261 [cl_62561,cl_62559,cl_40879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_40879 v h) (by intro d hd; cases hd))))
def cl_64264 : CNF.NClause := [(120,true),(58,false),(54,false)]
theorem der_64264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64264 :=
  CNF.rup_sound cl_64264 [cl_62561,cl_50474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50474 v h) (by intro d hd; cases hd)))
def cl_64269 : CNF.NClause := [(42,false),(121,true),(53,false)]
theorem der_64269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64269 :=
  CNF.rup_sound cl_64269 [cl_62561,cl_42429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_42429 v h) (by intro d hd; cases hd)))
def cl_64270 : CNF.NClause := [(122,true),(49,false),(37,false)]
theorem der_64270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64270 :=
  CNF.rup_sound cl_64270 [cl_62561,cl_42474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_42474 v h) (by intro d hd; cases hd)))
def cl_64271 : CNF.NClause := [(118,true),(34,false),(35,false)]
theorem der_64271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64271 :=
  CNF.rup_sound cl_64271 [cl_62561,cl_62559,cl_42604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_42604 v h) (by intro d hd; cases hd))))
def cl_64275 : CNF.NClause := [(93,true),(58,false),(59,false)]
theorem der_64275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64275 :=
  CNF.rup_sound cl_64275 [cl_62559,cl_55119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_55119 v h) (by intro d hd; cases hd)))
def cl_64277 : CNF.NClause := [(120,true),(47,false),(58,false)]
theorem der_64277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64277 :=
  CNF.rup_sound cl_64277 [cl_62561,cl_50492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50492 v h) (by intro d hd; cases hd)))
def cl_64278 : CNF.NClause := [(98,true),(51,false),(54,false)]
theorem der_64278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64278 :=
  CNF.rup_sound cl_64278 [cl_62559,cl_43460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_43460 v h) (by intro d hd; cases hd)))
def cl_64279 : CNF.NClause := [(52,false),(54,false),(98,true)]
theorem der_64279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64279 :=
  CNF.rup_sound cl_64279 [cl_62559,cl_50496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_50496 v h) (by intro d hd; cases hd)))
def cl_64281 : CNF.NClause := [(108,true),(49,false),(48,false)]
theorem der_64281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64281 :=
  CNF.rup_sound cl_64281 [cl_62559,cl_42480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_42480 v h) (by intro d hd; cases hd)))
def cl_64282 : CNF.NClause := [(111,false),(116,false),(68,false),(34,false),(63,false),(70,false),(4,false),(48,false),(14,true),(79,false),(78,false),(73,false),(106,false),(83,false),(96,false),(87,false)]
theorem der_64282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64282 :=
  CNF.rup_sound cl_64282 [cl_62561,cl_53169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_53169 v h) (by intro d hd; cases hd)))
def cl_64284 : CNF.NClause := [(98,false),(96,false),(27,false),(12,false),(83,false),(78,false),(105,false),(48,true),(79,false),(24,false),(71,false),(89,false),(112,false),(85,false),(54,false),(26,false),(75,false),(69,false),(76,false)]
theorem der_64284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64284 :=
  CNF.rup_sound cl_64284 [cl_62561,cl_44864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_44864 v h) (by intro d hd; cases hd)))
def cl_64285 : CNF.NClause := [(46,false),(123,false),(83,false),(68,false),(80,false),(9,true),(17,false),(76,false),(42,true),(109,false),(29,false),(64,false),(62,false),(86,false),(70,false),(110,false),(74,false),(77,false),(112,false)]
theorem der_64285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64285 :=
  CNF.rup_sound cl_64285 [cl_62559,cl_44264] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_44264 v h) (by intro d hd; cases hd)))
def cl_64291 : CNF.NClause := [(51,false),(69,false),(45,true),(48,false),(2,false),(15,false),(81,false),(109,false),(92,false),(34,false),(54,false),(74,false),(79,false),(80,false),(78,false),(87,false),(84,false),(77,false),(64,false)]
theorem der_64291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64291 :=
  CNF.rup_sound cl_64291 [cl_62559,cl_55280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_55280 v h) (by intro d hd; cases hd)))
def cl_64296 : CNF.NClause := [(120,true),(58,false),(45,false)]
theorem der_64296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64296 :=
  CNF.rup_sound cl_64296 [cl_62561,cl_45954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_45954 v h) (by intro d hd; cases hd)))
def cl_64302 : CNF.NClause := [(108,true),(46,false),(50,false)]
theorem der_64302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64302 :=
  CNF.rup_sound cl_64302 [cl_62559,cl_45747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_45747 v h) (by intro d hd; cases hd)))
def cl_64303 : CNF.NClause := [(108,true),(46,false),(47,false)]
theorem der_64303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64303 :=
  CNF.rup_sound cl_64303 [cl_62559,cl_45892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_45892 v h) (by intro d hd; cases hd)))
def cl_64307 : CNF.NClause := [(33,false),(109,false),(35,false),(80,false),(104,false),(76,false),(79,false),(91,false),(64,false),(114,false),(63,false),(99,false),(24,false),(74,false),(67,false),(69,false)]
theorem der_64307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64307 :=
  CNF.rup_sound cl_64307 [cl_62559,cl_62561,cl_55530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_55530 v h) (by intro d hd; cases hd))))
def cl_64310 : CNF.NClause := [(20,false),(111,false),(77,false),(69,false),(19,false),(112,false),(70,false),(109,false),(67,false),(110,false),(85,false),(74,false),(68,false),(46,false),(92,false),(63,false),(90,false)]
theorem der_64310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64310 :=
  CNF.rup_sound cl_64310 [cl_62561,cl_62559,cl_55606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_55606 v h) (by intro d hd; cases hd))))
def cl_64311 : CNF.NClause := [(120,true),(45,false),(54,false)]
theorem der_64311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64311 :=
  CNF.rup_sound cl_64311 [cl_62561,cl_46056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_46056 v h) (by intro d hd; cases hd)))
def cl_64320 : CNF.NClause := [(119,false),(96,false),(85,false),(44,false),(79,false),(102,false),(109,false),(42,true),(2,false),(74,false),(87,false),(6,false),(69,false),(84,false),(72,false),(81,false),(12,false),(68,false)]
theorem der_64320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64320 :=
  CNF.rup_sound cl_64320 [cl_62559,cl_54320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_54320 v h) (by intro d hd; cases hd)))
def cl_64327 : CNF.NClause := [(60,false),(51,false),(58,false),(120,false),(54,false),(46,false),(36,false),(33,true),(32,false)]
theorem der_64327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64327 :=
  CNF.rup_sound cl_64327 [cl_62559,cl_55686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_55686 v h) (by intro d hd; cases hd)))
def cl_64332 : CNF.NClause := [(103,true),(45,false),(41,true),(44,false)]
theorem der_64332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64332 :=
  CNF.rup_sound cl_64332 [cl_62559,cl_54184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_54184 v h) (by intro d hd; cases hd)))
def cl_64335 : CNF.NClause := [(2,false),(17,false),(13,false),(34,false),(70,false),(69,false),(77,false),(54,false),(51,false),(46,false),(76,false),(79,false),(65,false),(28,true),(72,false),(74,false),(87,false),(78,false),(83,false),(64,false),(71,false)]
theorem der_64335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64335 :=
  CNF.rup_sound cl_64335 [cl_62559,cl_62561,cl_55790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_55790 v h) (by intro d hd; cases hd))))
def cl_64336 : CNF.NClause := [(42,false),(51,false),(48,false),(34,false),(120,false),(47,false),(115,false)]
theorem der_64336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64336 :=
  CNF.rup_sound cl_64336 [cl_62559,cl_55746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_55746 v h) (by intro d hd; cases hd)))
def cl_64337 : CNF.NClause := [(60,false),(120,false),(51,false),(33,true),(58,false),(46,false),(36,false),(96,false),(54,false)]
theorem der_64337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64337 :=
  CNF.rup_sound cl_64337 [cl_62559,cl_52901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_52901 v h) (by intro d hd; cases hd)))
def cl_64338 : CNF.NClause := [(96,false),(70,false),(86,false),(80,false),(85,false),(74,false),(64,false),(17,false),(77,false),(83,false),(9,true),(33,true),(98,false),(68,false),(78,false),(29,false),(54,false),(89,false),(112,false),(69,false),(27,false)]
theorem der_64338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64338 :=
  CNF.rup_sound cl_64338 [cl_62561,cl_47858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_47858 v h) (by intro d hd; cases hd)))
def cl_64341 : CNF.NClause := [(52,true),(5,false),(82,false),(35,true),(74,false),(79,false),(34,false),(96,false),(3,false),(2,false),(22,false),(92,false),(111,false),(64,false),(69,false),(106,false),(101,false),(83,false)]
theorem der_64341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64341 :=
  CNF.rup_sound cl_64341 [cl_62559,cl_53244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_53244 v h) (by intro d hd; cases hd)))
def cl_64344 : CNF.NClause := [(111,false),(35,true),(64,false),(47,false),(77,false),(101,false),(2,false),(69,false),(79,false),(75,false),(87,false),(34,false),(89,false),(116,false),(74,false),(96,false)]
theorem der_64344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64344 :=
  CNF.rup_sound cl_64344 [cl_62559,cl_62561,cl_53214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_53214 v h) (by intro d hd; cases hd))))
def cl_64345 : CNF.NClause := [(2,false),(13,true),(99,false),(74,false),(69,false),(76,false),(104,false),(6,false),(114,false),(35,false),(109,false),(79,false),(67,false),(87,false),(63,false),(24,false),(64,false),(80,false)]
theorem der_64345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64345 :=
  CNF.rup_sound cl_64345 [cl_62559,cl_62561,cl_55708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_55708 v h) (by intro d hd; cases hd))))
def cl_64346 : CNF.NClause := [(113,true),(38,false),(40,true),(39,false)]
theorem der_64346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64346 :=
  CNF.rup_sound cl_64346 [cl_62559,cl_53661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_53661 v h) (by intro d hd; cases hd)))
def cl_64348 : CNF.NClause := [(120,true),(38,false),(47,false)]
theorem der_64348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64348 :=
  CNF.rup_sound cl_64348 [cl_62561,cl_50513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_50513 v h) (by intro d hd; cases hd)))
def cl_64351 : CNF.NClause := [(96,false),(47,true),(37,false),(39,false),(119,false),(101,false),(97,false),(42,true),(102,false),(44,false),(43,false),(105,false)]
theorem der_64351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64351 :=
  CNF.rup_sound cl_64351 [cl_62559,cl_53679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_53679 v h) (by intro d hd; cases hd)))
def cl_64358 : CNF.NClause := [(119,true),(40,false),(44,false)]
theorem der_64358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64358 :=
  CNF.rup_sound cl_64358 [cl_62561,cl_49745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_49745 v h) (by intro d hd; cases hd)))
def cl_64359 : CNF.NClause := [(119,true),(52,false),(48,false)]
theorem der_64359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64359 :=
  CNF.rup_sound cl_64359 [cl_62561,cl_49584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_49584 v h) (by intro d hd; cases hd)))
def cl_64365 : CNF.NClause := [(108,true),(50,false),(48,false)]
theorem der_64365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64365 :=
  CNF.rup_sound cl_64365 [cl_62559,cl_48917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_48917 v h) (by intro d hd; cases hd)))
def cl_64372 : CNF.NClause := [(113,false),(96,false),(84,false),(66,false),(39,false),(71,false),(63,false),(50,false),(90,false),(110,false),(75,false),(89,false),(107,false),(68,false),(16,false)]
theorem der_64372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64372 :=
  CNF.rup_sound cl_64372 [cl_62561,cl_54755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54755 v h) (by intro d hd; cases hd)))
def cl_64373 : CNF.NClause := [(42,false),(121,true),(50,false)]
theorem der_64373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64373 :=
  CNF.rup_sound cl_64373 [cl_62561,cl_49569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_49569 v h) (by intro d hd; cases hd)))
def cl_64374 : CNF.NClause := [(46,false),(109,false),(47,false),(111,false),(5,false),(112,false),(75,false),(68,false),(92,false),(86,false),(85,false),(77,false),(82,false),(83,false),(110,false),(89,false)]
theorem der_64374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64374 :=
  CNF.rup_sound cl_64374 [cl_62559,cl_62561,cl_55715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_55715 v h) (by intro d hd; cases hd))))
def cl_64377 : CNF.NClause := [(13,false),(44,false),(68,false),(70,false),(74,false),(85,false),(89,false),(81,false),(77,false),(47,false),(55,false),(17,false),(66,false),(82,false),(33,true),(6,false),(67,false),(34,true),(43,false),(83,false),(64,false),(23,false),(78,false),(76,false)]
theorem der_64377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64377 :=
  CNF.rup_sound cl_64377 [cl_62561,cl_62559,cl_53442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_53442 v h) (by intro d hd; cases hd))))
def cl_64378 : CNF.NClause := [(122,true),(57,false),(55,false),(43,true)]
theorem der_64378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64378 :=
  CNF.rup_sound cl_64378 [cl_62561,cl_54025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_54025 v h) (by intro d hd; cases hd)))
def cl_64381 : CNF.NClause := [(96,false),(58,false),(113,false),(119,false),(99,false),(52,false),(39,false),(53,false),(97,false),(110,false),(116,false)]
theorem der_64381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64381 :=
  CNF.rup_sound cl_64381 [cl_62559,cl_54431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_54431 v h) (by intro d hd; cases hd)))
def cl_64459 : CNF.NClause := [(103,true),(41,false),(44,false)]
theorem der_64459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64459 :=
  CNF.rup_sound cl_64459 [cl_62559,cl_56321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_56321 v h) (by intro d hd; cases hd)))
def cl_64460 : CNF.NClause := [(103,true),(41,false),(43,false)]
theorem der_64460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64460 :=
  CNF.rup_sound cl_64460 [cl_62559,cl_59267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_59267 v h) (by intro d hd; cases hd)))
def cl_64488 : CNF.NClause := [(39,false),(49,false),(59,false),(55,false),(58,false),(117,false),(108,false),(112,false)]
theorem der_64488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64488 :=
  CNF.rup_sound cl_64488 [cl_62559,cl_62561,cl_57941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57941 v h) (by intro d hd; cases hd))))
def cl_64558 : CNF.NClause := [(103,true),(45,false),(44,false)]
theorem der_64558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64558 :=
  CNF.rup_sound cl_64558 [cl_62559,cl_56365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_56365 v h) (by intro d hd; cases hd)))
def cl_64560 : CNF.NClause := [(45,false),(89,false),(91,false),(116,false),(69,false),(105,false),(18,false),(77,false),(72,false),(50,false),(70,false),(65,false),(73,false),(46,true),(121,false),(102,false)]
theorem der_64560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64560 :=
  CNF.rup_sound cl_64560 [cl_62559,cl_59380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_59380 v h) (by intro d hd; cases hd)))
def cl_64596 : CNF.NClause := [(49,false),(93,false),(40,false),(55,false),(39,false),(117,false),(108,false),(59,false),(54,true)]
theorem der_64596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64596 :=
  CNF.rup_sound cl_64596 [cl_62561,cl_57970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57970 v h) (by intro d hd; cases hd)))
def cl_64694 : CNF.NClause := [(45,false),(58,false),(37,false),(32,false),(44,false),(40,false),(52,false)]
theorem der_64694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64694 :=
  CNF.rup_sound cl_64694 [cl_62559,cl_62561,cl_58217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_58217 v h) (by intro d hd; cases hd))))
def cl_64722 : CNF.NClause := [(100,false),(43,true),(75,false),(68,false),(90,false),(71,false),(63,false),(84,false),(85,false),(109,false),(58,false),(74,false),(16,false),(19,false),(66,false),(93,false),(89,false),(107,false)]
theorem der_64722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64722 :=
  CNF.rup_sound cl_64722 [cl_62561,cl_56140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_56140 v h) (by intro d hd; cases hd)))
def cl_64745 : CNF.NClause := [(111,false),(107,false),(67,false),(78,false),(115,false),(91,false),(55,false),(12,false),(75,false),(72,false),(94,false),(22,false),(81,false),(68,false),(86,false),(85,false),(90,false)]
theorem der_64745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64745 :=
  CNF.rup_sound cl_64745 [cl_62559,cl_62561,cl_56116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_56116 v h) (by intro d hd; cases hd))))
def cl_64752 : CNF.NClause := [(59,true),(79,false),(64,false),(121,false),(53,true),(76,false),(42,true),(65,false),(86,false),(146,false),(78,false),(75,false)]
theorem der_64752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64752 :=
  CNF.rup_sound cl_64752 [cl_62561,cl_57365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57365 v h) (by intro d hd; cases hd)))
def cl_64780 : CNF.NClause := [(108,true),(49,false),(47,false)]
theorem der_64780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64780 :=
  CNF.rup_sound cl_64780 [cl_62559,cl_56643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_56643 v h) (by intro d hd; cases hd)))
def cl_64857 : CNF.NClause := [(60,false),(142,false),(6,false),(5,true),(58,false),(78,false),(96,false),(73,false),(82,false),(77,false),(66,false),(47,false),(69,false),(104,false),(70,false),(36,true),(74,false),(65,false)]
theorem der_64857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64857 :=
  CNF.rup_sound cl_64857 [cl_62559,cl_62561,cl_57082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57082 v h) (by intro d hd; cases hd))))
def cl_64888 : CNF.NClause := [(102,false),(40,false),(147,true),(88,false),(81,false),(68,false),(44,false),(76,false),(142,true),(79,false),(137,false),(70,false),(87,false),(80,false),(103,false),(65,false),(109,false),(69,false),(85,false),(19,false),(115,false)]
theorem der_64888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64888 :=
  CNF.rup_sound cl_64888 [cl_62561,cl_57516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57516 v h) (by intro d hd; cases hd)))
def cl_64952 : CNF.NClause := [(119,true),(60,false),(44,false)]
theorem der_64952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64952 :=
  CNF.rup_sound cl_64952 [cl_62561,cl_57415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57415 v h) (by intro d hd; cases hd)))
def cl_64956 : CNF.NClause := [(47,false),(15,false),(74,false),(75,false),(36,true),(77,false),(58,false),(73,false),(79,false),(76,false),(10,false),(80,false),(13,false),(60,false),(78,false),(52,false),(44,false),(81,false)]
theorem der_64956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64956 :=
  CNF.rup_sound cl_64956 [cl_62559,cl_57331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_57331 v h) (by intro d hd; cases hd)))
def cl_64958 : CNF.NClause := [(123,false),(113,false),(106,false),(99,false),(51,false),(44,false),(101,false),(35,true),(54,true),(55,false),(119,false),(40,false),(100,false)]
theorem der_64958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_64958 :=
  CNF.rup_sound cl_64958 [cl_62559,cl_56291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_56291 v h) (by intro d hd; cases hd)))
def cl_65025 : CNF.NClause := [(118,true),(34,false),(32,false)]
theorem der_65025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65025 :=
  CNF.rup_sound cl_65025 [cl_62559,cl_62561,cl_57206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57206 v h) (by intro d hd; cases hd))))
def cl_65062 : CNF.NClause := [(119,true),(40,false),(60,false)]
theorem der_65062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65062 :=
  CNF.rup_sound cl_65062 [cl_62561,cl_57656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57656 v h) (by intro d hd; cases hd)))
def cl_65072 : CNF.NClause := [(60,false),(49,false),(40,false),(37,false),(45,false),(47,false),(44,false),(54,true)]
theorem der_65072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65072 :=
  CNF.rup_sound cl_65072 [cl_62559,cl_58047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_58047 v h) (by intro d hd; cases hd)))
def cl_65073 : CNF.NClause := [(58,false),(40,false),(44,false),(53,false),(59,false),(52,false),(45,false)]
theorem der_65073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65073 :=
  CNF.rup_sound cl_65073 [cl_62559,cl_62561,cl_57337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_57337 v h) (by intro d hd; cases hd))))
def cl_65112 : CNF.NClause := [(2,false),(94,false),(81,false),(101,false),(66,false),(45,false),(44,false),(1,false),(120,false),(84,false),(86,false),(76,false),(78,false),(88,false),(110,false)]
theorem der_65112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65112 :=
  CNF.rup_sound cl_65112 [cl_62559,cl_59890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_59890 v h) (by intro d hd; cases hd)))
def cl_65113 : CNF.NClause := [(103,true),(45,false),(41,false),(42,true)]
theorem der_65113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65113 :=
  CNF.rup_sound cl_65113 [cl_62559,cl_59899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_59899 v h) (by intro d hd; cases hd)))
def cl_65120 : CNF.NClause := [(58,false),(89,false),(141,true),(100,false),(74,false),(79,false),(143,true),(84,false),(68,false),(7,true),(78,false),(76,false),(142,true),(75,false),(72,false),(73,false),(93,false),(11,true),(10,false),(81,false),(116,false),(139,false)]
theorem der_65120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65120 :=
  CNF.rup_sound cl_65120 [cl_62561,cl_59970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_59970 v h) (by intro d hd; cases hd)))
def cl_65218 : CNF.NClause := [(93,false),(117,false),(60,false),(15,false),(44,true),(70,false),(72,false),(10,false),(80,false),(78,false),(99,false),(79,false),(75,false),(74,false),(81,false),(88,false),(64,false),(17,false),(83,false),(73,false)]
theorem der_65218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65218 :=
  CNF.rup_sound cl_65218 [cl_62561,cl_60526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_60526 v h) (by intro d hd; cases hd)))
def cl_65385 : CNF.NClause := [(121,true),(50,false),(53,false)]
theorem der_65385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65385 :=
  CNF.rup_sound cl_65385 [cl_62561,cl_61486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_61486 v h) (by intro d hd; cases hd)))
def cl_65409 : CNF.NClause := [(36,false),(104,false),(60,false),(37,false),(55,false),(42,true),(34,false),(35,false)]
theorem der_65409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65409 :=
  CNF.rup_sound cl_65409 [cl_62561,cl_62559,cl_61692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_61692 v h) (by intro d hd; cases hd))))
def cl_65425 : CNF.NClause := [(119,true),(60,false),(52,false)]
theorem der_65425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65425 :=
  CNF.rup_sound cl_65425 [cl_62561,cl_61737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_61737 v h) (by intro d hd; cases hd)))
def cl_65428 : CNF.NClause := [(52,false),(88,false),(63,false),(55,false),(9,false),(92,false),(10,false),(36,false),(13,false),(81,false),(74,false),(82,false),(44,false),(76,false),(105,false),(73,false),(69,false)]
theorem der_65428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65428 :=
  CNF.rup_sound cl_65428 [cl_62559,cl_61758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_61758 v h) (by intro d hd; cases hd)))
def cl_65458 : CNF.NClause := [(58,false),(100,false),(35,false),(116,false),(47,false),(60,false),(48,false)]
theorem der_65458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65458 :=
  CNF.rup_sound cl_65458 [cl_62561,cl_61930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_61930 v h) (by intro d hd; cases hd)))
def cl_65470 : CNF.NClause := [(101,false),(10,false),(76,false),(3,false),(5,false),(39,true),(74,false),(122,false),(38,true),(86,false),(84,false),(82,false),(73,false),(37,false),(97,false),(12,false),(85,false),(109,false),(83,false)]
theorem der_65470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65470 :=
  CNF.rup_sound cl_65470 [cl_62559,cl_61970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_61970 v h) (by intro d hd; cases hd)))
def cl_65480 : CNF.NClause := [(151,false),(60,false),(44,false),(6,false),(43,false),(48,false),(40,false),(76,false),(84,false),(68,false),(77,false),(16,false),(3,false),(85,false),(69,false)]
theorem der_65480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65480 :=
  CNF.rup_sound cl_65480 [cl_62561,cl_62090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62090 v h) (by intro d hd; cases hd)))
def cl_65500 : CNF.NClause := [(44,false),(151,false),(71,false),(100,false),(59,false),(48,false),(85,false),(76,false),(7,false),(9,false),(50,false),(54,true),(64,false),(69,false),(73,false),(80,false)]
theorem der_65500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65500 :=
  CNF.rup_sound cl_65500 [cl_62561,cl_62212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62212 v h) (by intro d hd; cases hd)))
def cl_65550 : CNF.NClause := [(153,false),(74,true),(2,true)]
theorem der_65550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65550 :=
  CNF.rup_sound cl_65550 [cl_15794,cl_61744,cl_49952,cl_15772,cl_60450,cl_15789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_61744 v h) (hints_cons _ _ _ (der_49952 v h) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_60450 v h) (hints_cons _ _ _ (der_15789 v h) (by intro d hd; cases hd)))))))
def cl_65554 : CNF.NClause := [(147,false),(130,true),(153,true),(74,true),(143,true),(126,true)]
theorem der_65554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65554 :=
  CNF.rup_sound cl_65554 [cl_15789,cl_8041,cl_42451,cl_50171,cl_50105,cl_15776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (inp_8041 v h) (hints_cons _ _ _ (der_42451 v h) (hints_cons _ _ _ (der_50171 v h) (hints_cons _ _ _ (der_50105 v h) (hints_cons _ _ _ (der_15776 v h) (by intro d hd; cases hd)))))))
def cl_65562 : CNF.NClause := [(147,false),(153,true),(74,true),(143,true),(126,true)]
theorem der_65562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65562 :=
  CNF.rup_sound cl_65562 [cl_15789,cl_65554,cl_42451,cl_15772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_65554 v h) (hints_cons _ _ _ (der_42451 v h) (hints_cons _ _ _ (der_15772 v h) (by intro d hd; cases hd)))))
def cl_65566 : CNF.NClause := [(117,true),(45,true),(60,false),(53,false)]
theorem der_65566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65566 :=
  CNF.rup_sound cl_65566 [cl_50406,cl_50384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50406 v h) (hints_cons _ _ _ (der_50384 v h) (by intro d hd; cases hd)))
def cl_65568 : CNF.NClause := [(110,true),(45,false),(57,false)]
theorem der_65568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65568 :=
  CNF.rup_sound cl_65568 [cl_49935,cl_50323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49935 v h) (hints_cons _ _ _ (der_50323 v h) (by intro d hd; cases hd)))
def cl_65588 : CNF.NClause := [(130,false),(37,true),(74,false),(70,false),(18,false),(78,false)]
theorem der_65588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65588 :=
  CNF.rup_sound cl_65588 [cl_62573,cl_64072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62573 v h) (hints_cons _ _ _ (der_64072 v h) (by intro d hd; cases hd)))
def cl_65604 : CNF.NClause := [(150,false),(152,true),(101,false),(107,false),(80,false),(68,false),(108,false),(74,false),(71,false),(95,false),(48,false),(17,false),(83,false),(79,false),(91,false),(9,true),(151,true),(86,false),(75,false)]
theorem der_65604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65604 :=
  CNF.rup_sound cl_65604 [cl_15791,cl_15620,cl_60729,cl_7297,cl_53755,cl_63802,cl_63795,cl_7954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_60729 v h) (hints_cons _ _ _ (inp_7297 v h) (hints_cons _ _ _ (der_53755 v h) (hints_cons _ _ _ (der_63802 v h) (hints_cons _ _ _ (der_63795 v h) (hints_cons _ _ _ (inp_7954 v h) (by intro d hd; cases hd)))))))))
def cl_65616 : CNF.NClause := [(140,false),(68,true),(20,true)]
theorem der_65616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65616 :=
  CNF.rup_sound cl_65616 [cl_62405,cl_63563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62405 v h) (hints_cons _ _ _ (der_63563 v h) (by intro d hd; cases hd)))
def cl_65618 : CNF.NClause := [(132,false),(8,false),(20,true),(68,true)]
theorem der_65618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65618 :=
  CNF.rup_sound cl_65618 [cl_48942,cl_50185,cl_50071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48942 v h) (hints_cons _ _ _ (der_50185 v h) (hints_cons _ _ _ (der_50071 v h) (by intro d hd; cases hd))))
def cl_65619 : CNF.NClause := [(132,false),(68,true),(20,true)]
theorem der_65619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65619 :=
  CNF.rup_sound cl_65619 [cl_15774,cl_65618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_65618 v h) (by intro d hd; cases hd)))
def cl_65638 : CNF.NClause := [(143,true),(94,false),(115,false),(98,false),(85,false),(55,false),(3,false),(80,false),(62,false),(150,false),(81,false),(137,true),(76,false),(141,false),(83,false),(70,false),(79,false),(49,true),(65,false),(91,false),(142,true),(144,true),(139,true),(7,true),(86,false),(75,false)]
theorem der_65638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65638 :=
  CNF.rup_sound cl_65638 [cl_15791,cl_15773,cl_15653,cl_8022,cl_64053,cl_15782,cl_56322,cl_15767,cl_7297,cl_54408,cl_57424,cl_50257,cl_49969,cl_55963,cl_7961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15653 v h) (hints_cons _ _ _ (inp_8022 v h) (hints_cons _ _ _ (der_64053 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_56322 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (inp_7297 v h) (hints_cons _ _ _ (der_54408 v h) (hints_cons _ _ _ (der_57424 v h) (hints_cons _ _ _ (der_50257 v h) (hints_cons _ _ _ (der_49969 v h) (hints_cons _ _ _ (der_55963 v h) (hints_cons _ _ _ (inp_7961 v h) (by intro d hd; cases hd))))))))))))))))
def cl_65642 : CNF.NClause := [(143,false),(74,true),(29,true)]
theorem der_65642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65642 :=
  CNF.rup_sound cl_65642 [cl_15785,cl_62672,cl_50106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_62672 v h) (hints_cons _ _ _ (der_50106 v h) (by intro d hd; cases hd))))
def cl_65647 : CNF.NClause := [(17,false),(48,true),(76,false),(88,false),(83,false),(70,false),(18,false),(64,false)]
theorem der_65647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65647 :=
  CNF.rup_sound cl_65647 [cl_49885,cl_6145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49885 v h) (hints_cons _ _ _ (inp_6145 v h) (by intro d hd; cases hd)))
def cl_65676 : CNF.NClause := [(63,true),(143,true),(138,false),(133,true)]
theorem der_65676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65676 :=
  CNF.rup_sound cl_65676 [cl_62565,cl_62592,cl_15623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62565 v h) (hints_cons _ _ _ (der_62592 v h) (hints_cons _ _ _ (der_15623 v h) (by intro d hd; cases hd))))
def cl_65682 : CNF.NClause := [(29,false),(98,false),(121,false),(80,false),(13,false),(106,false),(71,false),(95,false),(68,false),(62,false),(84,false),(74,false),(72,false),(65,false),(78,false),(53,false),(22,false)]
theorem der_65682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65682 :=
  CNF.rup_sound cl_65682 [cl_62022,cl_43010,cl_5633,cl_49164,cl_7959,cl_49525,cl_65566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62022 v h) (hints_cons _ _ _ (der_43010 v h) (hints_cons _ _ _ (inp_5633 v h) (hints_cons _ _ _ (der_49164 v h) (hints_cons _ _ _ (inp_7959 v h) (hints_cons _ _ _ (der_49525 v h) (hints_cons _ _ _ (der_65566 v h) (by intro d hd; cases hd))))))))
def cl_65683 : CNF.NClause := [(99,true),(3,false),(153,true),(76,false),(63,false),(43,false),(140,true),(68,false),(136,false),(83,false),(73,false),(9,true),(144,true),(90,false),(78,false)]
theorem der_65683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65683 :=
  CNF.rup_sound cl_65683 [cl_47014,cl_49858,cl_62665,cl_63559,cl_8007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47014 v h) (hints_cons _ _ _ (der_49858 v h) (hints_cons _ _ _ (der_62665 v h) (hints_cons _ _ _ (der_63559 v h) (hints_cons _ _ _ (inp_8007 v h) (by intro d hd; cases hd))))))
def cl_65687 : CNF.NClause := [(23,false),(54,true),(74,false),(81,false),(83,false),(14,false),(65,false),(67,false)]
theorem der_65687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65687 :=
  CNF.rup_sound cl_65687 [cl_49783,cl_6913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49783 v h) (hints_cons _ _ _ (inp_6913 v h) (by intro d hd; cases hd)))
def cl_65690 : CNF.NClause := [(3,false),(119,false),(115,false),(103,false),(109,false),(44,false),(76,false),(66,false),(1,false),(71,false),(80,false),(51,true),(136,false),(70,false),(65,false),(86,false),(75,false)]
theorem der_65690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65690 :=
  CNF.rup_sound cl_65690 [cl_62572,cl_61053,cl_58161,cl_57424,cl_55464,cl_49198,cl_7950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62572 v h) (hints_cons _ _ _ (der_61053 v h) (hints_cons _ _ _ (der_58161 v h) (hints_cons _ _ _ (der_57424 v h) (hints_cons _ _ _ (der_55464 v h) (hints_cons _ _ _ (der_49198 v h) (hints_cons _ _ _ (inp_7950 v h) (by intro d hd; cases hd))))))))
def cl_65696 : CNF.NClause := [(117,true),(60,false),(53,false)]
theorem der_65696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65696 :=
  CNF.rup_sound cl_65696 [cl_49525,cl_65566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49525 v h) (hints_cons _ _ _ (der_65566 v h) (by intro d hd; cases hd)))
def cl_65699 : CNF.NClause := [(3,false),(107,false),(128,false),(115,false),(122,false),(98,false),(55,false),(80,false),(63,false),(85,false),(83,false),(70,false),(73,false),(65,false),(78,false),(75,false)]
theorem der_65699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65699 :=
  CNF.rup_sound cl_65699 [cl_15770,cl_62665,cl_42525,cl_55640,cl_4353,cl_7961,cl_49969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_62665 v h) (hints_cons _ _ _ (der_42525 v h) (hints_cons _ _ _ (der_55640 v h) (hints_cons _ _ _ (inp_4353 v h) (hints_cons _ _ _ (inp_7961 v h) (hints_cons _ _ _ (der_49969 v h) (by intro d hd; cases hd))))))))
def cl_65702 : CNF.NClause := [(3,false),(4,false),(34,true),(80,false),(85,false),(70,false),(65,false),(75,false)]
theorem der_65702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65702 :=
  CNF.rup_sound cl_65702 [cl_4353,cl_42525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4353 v h) (hints_cons _ _ _ (der_42525 v h) (by intro d hd; cases hd)))
def cl_65706 : CNF.NClause := [(103,true),(45,false),(43,false),(42,true)]
theorem der_65706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65706 :=
  CNF.rup_sound cl_65706 [cl_64213,cl_57712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64213 v h) (hints_cons _ _ _ (der_57712 v h) (by intro d hd; cases hd)))
def cl_65712 : CNF.NClause := [(76,true),(140,true),(147,true),(143,true),(153,true),(69,true),(135,true),(146,false)]
theorem der_65712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65712 :=
  CNF.rup_sound cl_65712 [cl_62463,cl_56888,cl_56868,cl_61991,cl_63761,cl_54207,cl_8044,cl_15643,cl_15636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62463 v h) (hints_cons _ _ _ (der_56888 v h) (hints_cons _ _ _ (der_56868 v h) (hints_cons _ _ _ (der_61991 v h) (hints_cons _ _ _ (der_63761 v h) (hints_cons _ _ _ (der_54207 v h) (hints_cons _ _ _ (inp_8044 v h) (hints_cons _ _ _ (der_15643 v h) (hints_cons _ _ _ (der_15636 v h) (by intro d hd; cases hd))))))))))
def cl_65714 : CNF.NClause := [(152,true),(137,true),(147,true),(143,true),(153,true),(136,false),(69,true),(139,true),(131,true)]
theorem der_65714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65714 :=
  CNF.rup_sound cl_65714 [cl_62463,cl_62196,cl_56888,cl_15620,cl_8085,cl_8027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62463 v h) (hints_cons _ _ _ (der_62196 v h) (hints_cons _ _ _ (der_56888 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (inp_8085 v h) (hints_cons _ _ _ (inp_8027 v h) (by intro d hd; cases hd)))))))
def cl_65716 : CNF.NClause := [(80,false),(39,false),(32,false),(3,false),(24,false),(106,false),(1,false),(59,false),(84,false),(76,false),(43,false),(63,false),(85,false),(70,false),(49,true),(65,false),(91,false),(146,false)]
theorem der_65716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65716 :=
  CNF.rup_sound cl_65716 [cl_63071,cl_62576,cl_7041,cl_58161,cl_49955,cl_50033,cl_49969,cl_65025,cl_54873,cl_7940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_62576 v h) (hints_cons _ _ _ (inp_7041 v h) (hints_cons _ _ _ (der_58161 v h) (hints_cons _ _ _ (der_49955 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_49969 v h) (hints_cons _ _ _ (der_65025 v h) (hints_cons _ _ _ (der_54873 v h) (hints_cons _ _ _ (inp_7940 v h) (by intro d hd; cases hd)))))))))))
def cl_65720 : CNF.NClause := [(153,false),(152,true),(13,false),(83,true),(70,false),(142,true),(151,true),(11,true),(7,true),(86,false),(78,false)]
theorem der_65720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65720 :=
  CNF.rup_sound cl_65720 [cl_63963,cl_63585,cl_15777,cl_15794,cl_15617,cl_62022,cl_15791,cl_60233,cl_15789,cl_63367,cl_8094,cl_61589,cl_15771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63963 v h) (hints_cons _ _ _ (der_63585 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_62022 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_60233 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_63367 v h) (hints_cons _ _ _ (inp_8094 v h) (hints_cons _ _ _ (der_61589 v h) (hints_cons _ _ _ (der_15771 v h) (by intro d hd; cases hd))))))))))))))
def cl_65724 : CNF.NClause := [(129,false),(83,true),(11,true)]
theorem der_65724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65724 :=
  CNF.rup_sound cl_65724 [cl_15771,cl_54102,cl_61695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_54102 v h) (hints_cons _ _ _ (der_61695 v h) (by intro d hd; cases hd))))
def cl_65725 : CNF.NClause := [(150,false),(129,true),(128,true),(141,true),(83,true),(135,true)]
theorem der_65725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65725 :=
  CNF.rup_sound cl_65725 [cl_15791,cl_8094,cl_54213,cl_15789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (inp_8094 v h) (hints_cons _ _ _ (der_54213 v h) (hints_cons _ _ _ (der_15789 v h) (by intro d hd; cases hd)))))
def cl_65727 : CNF.NClause := [(21,false),(13,false),(117,false),(95,false),(106,false),(121,false),(84,false),(66,false),(71,false),(85,false),(72,false),(79,false),(73,false),(65,false),(9,true),(78,false),(53,false),(67,false)]
theorem der_65727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65727 :=
  CNF.rup_sound cl_65727 [cl_52799,cl_61034,cl_49164,cl_64217,cl_7959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52799 v h) (hints_cons _ _ _ (der_61034 v h) (hints_cons _ _ _ (der_49164 v h) (hints_cons _ _ _ (der_64217 v h) (hints_cons _ _ _ (inp_7959 v h) (by intro d hd; cases hd))))))
def cl_65736 : CNF.NClause := [(102,true),(50,false),(57,false),(44,false)]
theorem der_65736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65736 :=
  CNF.rup_sound cl_65736 [cl_51469,cl_35307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51469 v h) (hints_cons _ _ _ (der_35307 v h) (by intro d hd; cases hd)))
def cl_65737 : CNF.NClause := [(102,true),(57,false),(44,false)]
theorem der_65737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65737 :=
  CNF.rup_sound cl_65737 [cl_64042,cl_65736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64042 v h) (hints_cons _ _ _ (der_65736 v h) (by intro d hd; cases hd)))
def cl_65738 : CNF.NClause := [(85,true),(145,false),(21,false)]
theorem der_65738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65738 :=
  CNF.rup_sound cl_65738 [cl_54810,cl_60483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54810 v h) (hints_cons _ _ _ (der_60483 v h) (by intro d hd; cases hd)))
def cl_65746 : CNF.NClause := [(76,true),(141,false)]
theorem der_65746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65746 :=
  CNF.rup_sound cl_65746 [cl_15783,cl_42519,cl_63952,cl_15792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_42519 v h) (hints_cons _ _ _ (der_63952 v h) (hints_cons _ _ _ (der_15792 v h) (by intro d hd; cases hd)))))
def cl_65751 : CNF.NClause := [(85,true),(151,false)]
theorem der_65751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65751 :=
  CNF.rup_sound cl_65751 [cl_15792,cl_58006,cl_53985,cl_50155,cl_50391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_58006 v h) (hints_cons _ _ _ (der_53985 v h) (hints_cons _ _ _ (der_50155 v h) (hints_cons _ _ _ (der_50391 v h) (by intro d hd; cases hd))))))
def cl_65753 : CNF.NClause := [(129,false),(20,false),(36,true),(85,false),(84,false),(83,false),(86,false)]
theorem der_65753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65753 :=
  CNF.rup_sound cl_65753 [cl_15771,cl_62455,cl_29838,cl_4609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_62455 v h) (hints_cons _ _ _ (der_29838 v h) (hints_cons _ _ _ (inp_4609 v h) (by intro d hd; cases hd)))))
def cl_65759 : CNF.NClause := [(81,true),(152,false),(15,true)]
theorem der_65759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65759 :=
  CNF.rup_sound cl_65759 [cl_15793,cl_61226,cl_63753,cl_15775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_61226 v h) (hints_cons _ _ _ (der_63753 v h) (hints_cons _ _ _ (der_15775 v h) (by intro d hd; cases hd)))))
def cl_65773 : CNF.NClause := [(81,true),(133,false),(9,false),(15,true)]
theorem der_65773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65773 :=
  CNF.rup_sound cl_65773 [cl_61806,cl_61226,cl_61052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61806 v h) (hints_cons _ _ _ (der_61226 v h) (hints_cons _ _ _ (der_61052 v h) (by intro d hd; cases hd))))
def cl_65774 : CNF.NClause := [(59,false),(40,false),(93,false),(49,false),(48,false),(44,false),(42,true),(53,false)]
theorem der_65774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65774 :=
  CNF.rup_sound cl_65774 [cl_64178,cl_54282,cl_57876,cl_62370,cl_63179,cl_7965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64178 v h) (hints_cons _ _ _ (der_54282 v h) (hints_cons _ _ _ (der_57876 v h) (hints_cons _ _ _ (der_62370 v h) (hints_cons _ _ _ (der_63179 v h) (hints_cons _ _ _ (inp_7965 v h) (by intro d hd; cases hd)))))))
def cl_65781 : CNF.NClause := [(2,false),(79,true),(26,false)]
theorem der_65781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65781 :=
  CNF.rup_sound cl_65781 [cl_53840,cl_37816,cl_51506,cl_51508] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53840 v h) (hints_cons _ _ _ (der_37816 v h) (hints_cons _ _ _ (der_51506 v h) (hints_cons _ _ _ (der_51508 v h) (by intro d hd; cases hd)))))
def cl_65811 : CNF.NClause := [(133,false),(40,true),(81,false),(88,false),(17,false),(69,false),(75,false)]
theorem der_65811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65811 :=
  CNF.rup_sound cl_65811 [cl_62190,cl_62333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62190 v h) (hints_cons _ _ _ (der_62333 v h) (by intro d hd; cases hd)))
def cl_65820 : CNF.NClause := [(145,false),(52,true),(73,false),(85,false),(88,false),(135,true),(67,false)]
theorem der_65820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65820 :=
  CNF.rup_sound cl_65820 [cl_56741,cl_56859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56741 v h) (hints_cons _ _ _ (der_56859 v h) (by intro d hd; cases hd)))
def cl_65835 : CNF.NClause := [(38,false),(89,false),(7,true),(71,false),(73,false),(64,false)]
theorem der_65835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65835 :=
  CNF.rup_sound cl_65835 [cl_60061,cl_52486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60061 v h) (hints_cons _ _ _ (der_52486 v h) (by intro d hd; cases hd)))
def cl_65849 : CNF.NClause := [(68,true),(140,false)]
theorem der_65849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65849 :=
  CNF.rup_sound cl_65849 [cl_15782,cl_65616,cl_62409,cl_54107,cl_50096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_65616 v h) (hints_cons _ _ _ (der_62409 v h) (hints_cons _ _ _ (der_54107 v h) (hints_cons _ _ _ (der_50096 v h) (by intro d hd; cases hd))))))
def cl_65850 : CNF.NClause := [(63,true),(138,false),(143,true)]
theorem der_65850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65850 :=
  CNF.rup_sound cl_65850 [cl_62149,cl_65676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62149 v h) (hints_cons _ _ _ (der_65676 v h) (by intro d hd; cases hd)))
def cl_65851 : CNF.NClause := [(152,true),(57,true),(151,true),(153,false),(79,false),(71,false),(91,false),(83,false),(75,false)]
theorem der_65851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65851 :=
  CNF.rup_sound cl_65851 [cl_15617,cl_15791,cl_60729,cl_7297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_60729 v h) (hints_cons _ _ _ (inp_7297 v h) (by intro d hd; cases hd)))))
def cl_65857 : CNF.NClause := [(133,false),(81,true),(15,true)]
theorem der_65857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65857 :=
  CNF.rup_sound cl_65857 [cl_15775,cl_65773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_65773 v h) (by intro d hd; cases hd)))
def cl_65861 : CNF.NClause := [(152,false),(57,true),(151,true),(153,true),(79,false),(71,false),(91,false),(83,false),(75,false)]
theorem der_65861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65861 :=
  CNF.rup_sound cl_65861 [cl_15793,cl_15618,cl_37572,cl_15791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_15618 v h) (hints_cons _ _ _ (der_37572 v h) (hints_cons _ _ _ (der_15791 v h) (by intro d hd; cases hd)))))
def cl_65888 : CNF.NClause := [(84,true),(5,false),(16,false)]
theorem der_65888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65888 :=
  CNF.rup_sound cl_65888 [cl_50199,cl_42738,cl_50198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50199 v h) (hints_cons _ _ _ (der_42738 v h) (hints_cons _ _ _ (der_50198 v h) (by intro d hd; cases hd))))
def cl_65889 : CNF.NClause := [(84,true),(140,false)]
theorem der_65889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65889 :=
  CNF.rup_sound cl_65889 [cl_15782,cl_59321,cl_65888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_59321 v h) (hints_cons _ _ _ (der_65888 v h) (by intro d hd; cases hd))))
def cl_65890 : CNF.NClause := [(85,true),(147,true),(133,true),(125,true),(136,true),(151,true),(137,true),(140,false),(143,true),(142,true),(135,true),(131,true)]
theorem der_65890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65890 :=
  CNF.rup_sound cl_65890 [cl_62591,cl_63986,cl_15634,cl_8107,cl_15659,cl_15637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62591 v h) (hints_cons _ _ _ (der_63986 v h) (hints_cons _ _ _ (der_15634 v h) (hints_cons _ _ _ (inp_8107 v h) (hints_cons _ _ _ (der_15659 v h) (hints_cons _ _ _ (der_15637 v h) (by intro d hd; cases hd)))))))
def cl_65896 : CNF.NClause := [(134,false),(111,false),(20,false),(93,false),(119,false),(60,false),(117,false),(73,false),(71,false),(68,false),(74,false),(141,false),(69,false),(146,false)]
theorem der_65896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65896 :=
  CNF.rup_sound cl_65896 [cl_65746,cl_62587,cl_63071,cl_62576,cl_15776,cl_62595,cl_59719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65746 v h) (hints_cons _ _ _ (der_62587 v h) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_62576 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (der_62595 v h) (hints_cons _ _ _ (der_59719 v h) (by intro d hd; cases hd))))))))
def cl_65899 : CNF.NClause := [(107,true),(1,false),(63,false),(71,false),(48,false),(80,false),(81,false),(140,false),(91,false),(76,false),(15,true),(11,true),(7,true),(86,false),(67,false)]
theorem der_65899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65899 :=
  CNF.rup_sound cl_65899 [cl_65889,cl_56322,cl_42515,cl_49471,cl_48712,cl_57424,cl_48893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65889 v h) (hints_cons _ _ _ (der_56322 v h) (hints_cons _ _ _ (der_42515 v h) (hints_cons _ _ _ (der_49471 v h) (hints_cons _ _ _ (der_48712 v h) (hints_cons _ _ _ (der_57424 v h) (hints_cons _ _ _ (der_48893 v h) (by intro d hd; cases hd))))))))
def cl_65909 : CNF.NClause := [(147,false),(54,true),(81,false),(16,false),(142,true),(74,false),(17,false),(11,true),(7,true),(67,false)]
theorem der_65909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65909 :=
  CNF.rup_sound cl_65909 [cl_15789,cl_63419,cl_50418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_63419 v h) (hints_cons _ _ _ (der_50418 v h) (by intro d hd; cases hd))))
def cl_65919 : CNF.NClause := [(150,false),(79,true),(138,true)]
theorem der_65919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65919 :=
  CNF.rup_sound cl_65919 [cl_63081,cl_15791,cl_62991,cl_65781,cl_15768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63081 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_62991 v h) (hints_cons _ _ _ (der_65781 v h) (hints_cons _ _ _ (der_15768 v h) (by intro d hd; cases hd))))))
def cl_65937 : CNF.NClause := [(134,false),(43,true),(138,true),(85,false),(81,false),(137,true),(68,false),(91,false),(135,true),(64,false)]
theorem der_65937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65937 :=
  CNF.rup_sound cl_65937 [cl_62595,cl_15650,cl_5505,cl_15778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62595 v h) (hints_cons _ _ _ (der_15650 v h) (hints_cons _ _ _ (inp_5505 v h) (hints_cons _ _ _ (der_15778 v h) (by intro d hd; cases hd)))))
def cl_65946 : CNF.NClause := [(150,false),(107,false),(108,false),(101,false),(79,false),(95,false),(48,false),(88,false),(80,false),(29,false),(68,false),(143,true),(91,false),(74,false),(83,false),(7,true),(86,false),(75,false)]
theorem der_65946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65946 :=
  CNF.rup_sound cl_65946 [cl_15791,cl_29835,cl_36193,cl_63795,cl_7954,cl_63802,cl_7297,cl_62569,cl_64053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_29835 v h) (hints_cons _ _ _ (der_36193 v h) (hints_cons _ _ _ (der_63795 v h) (hints_cons _ _ _ (inp_7954 v h) (hints_cons _ _ _ (der_63802 v h) (hints_cons _ _ _ (inp_7297 v h) (hints_cons _ _ _ (der_62569 v h) (hints_cons _ _ _ (der_64053 v h) (by intro d hd; cases hd))))))))))
def cl_65951 : CNF.NClause := [(71,true),(150,false),(143,true),(7,true)]
theorem der_65951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65951 :=
  CNF.rup_sound cl_65951 [cl_62569,cl_64053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62569 v h) (hints_cons _ _ _ (der_64053 v h) (by intro d hd; cases hd)))
def cl_65980 : CNF.NClause := [(5,false),(38,true),(97,false),(122,false),(134,false),(101,false),(109,false),(37,false),(82,false),(85,false),(73,false),(138,true),(84,false),(74,false),(76,false),(83,false),(135,true),(86,false),(75,false)]
theorem der_65980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65980 :=
  CNF.rup_sound cl_65980 [cl_15776,cl_63577,cl_37437,cl_39346,cl_43711,cl_7943,cl_49913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (der_63577 v h) (hints_cons _ _ _ (der_37437 v h) (hints_cons _ _ _ (der_39346 v h) (hints_cons _ _ _ (der_43711 v h) (hints_cons _ _ _ (inp_7943 v h) (hints_cons _ _ _ (der_49913 v h) (by intro d hd; cases hd))))))))
def cl_65997 : CNF.NClause := [(132,false),(39,true),(68,false),(76,false),(90,false)]
theorem der_65997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_65997 :=
  CNF.rup_sound cl_65997 [cl_60459,cl_63081,cl_57439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60459 v h) (hints_cons _ _ _ (der_63081 v h) (hints_cons _ _ _ (der_57439 v h) (by intro d hd; cases hd))))
def cl_66000 : CNF.NClause := [(87,true),(4,false),(132,true),(148,true),(127,true),(150,true),(138,true),(137,true),(143,true),(142,true),(139,true),(131,true),(146,false)]
theorem der_66000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66000 :=
  CNF.rup_sound cl_66000 [cl_61797,cl_54172,cl_15767,cl_15768,cl_8023,cl_8071,cl_63771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61797 v h) (hints_cons _ _ _ (der_54172 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (inp_8023 v h) (hints_cons _ _ _ (inp_8071 v h) (hints_cons _ _ _ (der_63771 v h) (by intro d hd; cases hd))))))))
def cl_66003 : CNF.NClause := [(145,false),(33,true),(4,false),(132,true),(150,true),(138,true),(84,false),(74,false),(69,false),(139,true),(131,true)]
theorem der_66003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66003 :=
  CNF.rup_sound cl_66003 [cl_56741,cl_8071,cl_63359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56741 v h) (hints_cons _ _ _ (inp_8071 v h) (hints_cons _ _ _ (der_63359 v h) (by intro d hd; cases hd))))
def cl_66025 : CNF.NClause := [(5,false),(39,true),(119,false),(108,false),(95,false),(48,false),(101,false),(82,false),(10,false),(85,false),(73,false),(72,false),(84,false),(74,false),(76,false),(83,false),(86,false),(75,false)]
theorem der_66025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66025 :=
  CNF.rup_sound cl_66025 [cl_63577,cl_37437,cl_50024,cl_5249,cl_7954,cl_38818,cl_31968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63577 v h) (hints_cons _ _ _ (der_37437 v h) (hints_cons _ _ _ (der_50024 v h) (hints_cons _ _ _ (inp_5249 v h) (hints_cons _ _ _ (inp_7954 v h) (hints_cons _ _ _ (der_38818 v h) (hints_cons _ _ _ (der_31968 v h) (by intro d hd; cases hd))))))))
def cl_66045 : CNF.NClause := [(126,false),(125,false),(33,true),(32,true),(81,false),(84,false),(143,true),(74,false),(76,false),(69,false),(7,true),(86,false)]
theorem der_66045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66045 :=
  CNF.rup_sound cl_66045 [cl_15767,cl_15773,cl_15768,cl_58713,cl_59918,cl_65781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_58713 v h) (hints_cons _ _ _ (der_59918 v h) (hints_cons _ _ _ (der_65781 v h) (by intro d hd; cases hd)))))))
def cl_66105 : CNF.NClause := [(126,false),(107,false),(94,false),(122,false),(65,false),(127,false),(3,false),(153,true),(98,false),(55,false),(84,false),(79,false),(85,false),(74,false),(70,false),(69,false),(139,true),(11,true),(7,true),(75,false)]
theorem der_66105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66105 :=
  CNF.rup_sound cl_66105 [cl_15773,cl_15768,cl_59419,cl_59174,cl_36883,cl_49969,cl_7961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_59419 v h) (hints_cons _ _ _ (der_59174 v h) (hints_cons _ _ _ (der_36883 v h) (hints_cons _ _ _ (der_49969 v h) (hints_cons _ _ _ (inp_7961 v h) (by intro d hd; cases hd))))))))
def cl_66108 : CNF.NClause := [(84,true),(148,false)]
theorem der_66108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66108 :=
  CNF.rup_sound cl_66108 [cl_63775,cl_57714,cl_37830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63775 v h) (hints_cons _ _ _ (der_57714 v h) (hints_cons _ _ _ (der_37830 v h) (by intro d hd; cases hd))))
def cl_66126 : CNF.NClause := [(153,false),(60,true),(80,false),(62,false),(88,false),(74,false),(86,false)]
theorem der_66126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66126 :=
  CNF.rup_sound cl_66126 [cl_15794,cl_61595,cl_7681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_61595 v h) (hints_cons _ _ _ (inp_7681 v h) (by intro d hd; cases hd))))
def cl_66131 : CNF.NClause := [(153,false),(60,true),(62,false),(88,false),(74,false),(86,false)]
theorem der_66131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66131 :=
  CNF.rup_sound cl_66131 [cl_62562,cl_66126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62562 v h) (hints_cons _ _ _ (der_66126 v h) (by intro d hd; cases hd)))
def cl_66156 : CNF.NClause := [(68,true),(153,true),(144,false),(128,true)]
theorem der_66156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66156 :=
  CNF.rup_sound cl_66156 [cl_15786,cl_57410,cl_42497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_57410 v h) (hints_cons _ _ _ (der_42497 v h) (by intro d hd; cases hd))))
def cl_66178 : CNF.NClause := [(140,false),(47,true),(150,true),(89,false),(84,false),(77,false)]
theorem der_66178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66178 :=
  CNF.rup_sound cl_66178 [cl_65849,cl_57618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65849 v h) (hints_cons _ _ _ (der_57618 v h) (by intro d hd; cases hd)))
def cl_66186 : CNF.NClause := [(140,false),(117,false),(98,false),(89,false),(109,false),(150,true),(12,false),(72,false),(84,false),(81,false),(121,false),(85,false),(91,false),(77,false),(64,false),(53,false)]
theorem der_66186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66186 :=
  CNF.rup_sound cl_66186 [cl_65849,cl_57618,cl_5505,cl_57601,cl_63458,cl_7959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65849 v h) (hints_cons _ _ _ (der_57618 v h) (hints_cons _ _ _ (inp_5505 v h) (hints_cons _ _ _ (der_57601 v h) (hints_cons _ _ _ (der_63458 v h) (hints_cons _ _ _ (inp_7959 v h) (by intro d hd; cases hd)))))))
def cl_66199 : CNF.NClause := [(109,true),(88,false),(72,false),(65,false),(151,true),(84,false),(128,true),(71,false),(74,false),(70,false),(139,true),(18,false),(53,false),(146,false)]
theorem der_66199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66199 :=
  CNF.rup_sound cl_66199 [cl_63071,cl_62576,cl_15788,cl_51968,cl_60050,cl_49164,cl_65588,cl_5633,cl_8065,cl_15779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_62576 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_51968 v h) (hints_cons _ _ _ (der_60050 v h) (hints_cons _ _ _ (der_49164 v h) (hints_cons _ _ _ (der_65588 v h) (hints_cons _ _ _ (inp_5633 v h) (hints_cons _ _ _ (inp_8065 v h) (hints_cons _ _ _ (der_15779 v h) (by intro d hd; cases hd)))))))))))
def cl_66231 : CNF.NClause := [(132,false),(39,true),(79,false),(76,false),(90,false)]
theorem der_66231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66231 :=
  CNF.rup_sound cl_66231 [cl_65997,cl_61594,cl_65619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65997 v h) (hints_cons _ _ _ (der_61594 v h) (hints_cons _ _ _ (der_65619 v h) (by intro d hd; cases hd))))
def cl_66240 : CNF.NClause := [(1066,false),(68,true)]
theorem der_66240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66240 :=
  CNF.rup_sound cl_66240 [cl_15918,cl_62806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_62806 v h) (by intro d hd; cases hd)))
def cl_66321 : CNF.NClause := [(102,true),(38,true),(57,false),(50,false)]
theorem der_66321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66321 :=
  CNF.rup_sound cl_66321 [cl_31931,cl_65737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31931 v h) (hints_cons _ _ _ (der_65737 v h) (by intro d hd; cases hd)))
def cl_66359 : CNF.NClause := [(126,true),(36,true),(150,true),(152,true),(148,true),(140,false),(137,true),(127,true),(132,true),(138,true),(84,false),(85,false),(142,true),(83,false),(139,true),(86,false),(146,false)]
theorem der_66359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66359 :=
  CNF.rup_sound cl_66359 [cl_8071,cl_8102,cl_63771,cl_65753,cl_15786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8071 v h) (hints_cons _ _ _ (inp_8102 v h) (hints_cons _ _ _ (der_63771 v h) (hints_cons _ _ _ (der_65753 v h) (hints_cons _ _ _ (der_15786 v h) (by intro d hd; cases hd))))))
def cl_66372 : CNF.NClause := [(140,false),(47,true),(150,true),(14,false),(84,false),(68,false),(77,false),(7,true)]
theorem der_66372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66372 :=
  CNF.rup_sound cl_66372 [cl_15782,cl_57618,cl_50455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_57618 v h) (hints_cons _ _ _ (der_50455 v h) (by intro d hd; cases hd))))
def cl_66375 : CNF.NClause := [(20,false),(51,true),(10,false),(68,false),(71,false),(70,false),(69,false),(67,false)]
theorem der_66375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66375 :=
  CNF.rup_sound cl_66375 [cl_49778,cl_6529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49778 v h) (hints_cons _ _ _ (inp_6529 v h) (by intro d hd; cases hd)))
def cl_66383 : CNF.NClause := [(144,false),(133,true),(140,true),(36,true),(152,true),(137,true),(148,true),(84,false),(151,true),(85,false),(142,true),(83,false),(135,true),(86,false)]
theorem der_66383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66383 :=
  CNF.rup_sound cl_66383 [cl_15786,cl_8011,cl_65753,cl_8105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (inp_8011 v h) (hints_cons _ _ _ (der_65753 v h) (hints_cons _ _ _ (inp_8105 v h) (by intro d hd; cases hd)))))
def cl_66388 : CNF.NClause := [(126,false),(123,false),(51,false),(102,false),(101,false),(49,true),(98,false),(84,false),(128,false),(79,false),(63,false),(74,false),(83,false),(69,false),(131,true),(78,false)]
theorem der_66388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66388 :=
  CNF.rup_sound cl_66388 [cl_62171,cl_15770,cl_15768,cl_63359,cl_54172,cl_50270,cl_54056,cl_7957,cl_42999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_63359 v h) (hints_cons _ _ _ (der_54172 v h) (hints_cons _ _ _ (der_50270 v h) (hints_cons _ _ _ (der_54056 v h) (hints_cons _ _ _ (inp_7957 v h) (hints_cons _ _ _ (der_42999 v h) (by intro d hd; cases hd))))))))))
def cl_66405 : CNF.NClause := [(145,false),(52,true),(73,false),(79,false),(85,false),(17,false),(135,true),(67,false)]
theorem der_66405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66405 :=
  CNF.rup_sound cl_66405 [cl_15787,cl_56859,cl_49839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_56859 v h) (hints_cons _ _ _ (der_49839 v h) (by intro d hd; cases hd))))
def cl_66455 : CNF.NClause := [(107,true),(41,false),(39,true),(48,false)]
theorem der_66455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66455 :=
  CNF.rup_sound cl_66455 [cl_42515,cl_31968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42515 v h) (hints_cons _ _ _ (der_31968 v h) (by intro d hd; cases hd)))
def cl_66469 : CNF.NClause := [(140,false),(150,true),(47,true),(84,false),(27,false),(77,false)]
theorem der_66469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66469 :=
  CNF.rup_sound cl_66469 [cl_15782,cl_66178,cl_49824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_66178 v h) (hints_cons _ _ _ (der_49824 v h) (by intro d hd; cases hd))))
def cl_66472 : CNF.NClause := [(126,false),(102,false),(116,false),(45,true),(108,false),(84,false),(128,false),(79,false),(121,false),(50,false),(63,false),(74,false),(83,false),(69,false),(131,true),(78,false)]
theorem der_66472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66472 :=
  CNF.rup_sound cl_66472 [cl_62171,cl_15770,cl_15768,cl_63359,cl_54172,cl_49916,cl_54056,cl_7956,cl_63041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_63359 v h) (hints_cons _ _ _ (der_54172 v h) (hints_cons _ _ _ (der_49916 v h) (hints_cons _ _ _ (der_54056 v h) (hints_cons _ _ _ (inp_7956 v h) (hints_cons _ _ _ (der_63041 v h) (by intro d hd; cases hd))))))))))
def cl_66477 : CNF.NClause := [(133,true),(130,false),(126,true),(132,true),(36,true),(84,false),(151,false),(85,false),(142,true),(83,false),(135,true),(131,true),(86,false)]
theorem der_66477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66477 :=
  CNF.rup_sound cl_66477 [cl_8010,cl_15659,cl_15786,cl_65753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8010 v h) (hints_cons _ _ _ (der_15659 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_65753 v h) (by intro d hd; cases hd)))))
def cl_66480 : CNF.NClause := [(133,true),(132,true),(130,false),(126,true),(51,true),(84,false),(151,false),(68,false),(71,false),(85,false),(142,true),(83,false),(70,false),(69,false),(135,true),(131,true),(86,false),(67,false)]
theorem der_66480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66480 :=
  CNF.rup_sound cl_66480 [cl_8010,cl_66477,cl_15786,cl_63482,cl_6529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8010 v h) (hints_cons _ _ _ (der_66477 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_63482 v h) (hints_cons _ _ _ (inp_6529 v h) (by intro d hd; cases hd))))))
def cl_66483 : CNF.NClause := [(147,false),(54,true),(81,false),(27,false),(142,true),(74,false),(17,false),(11,true),(67,false)]
theorem der_66483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66483 :=
  CNF.rup_sound cl_66483 [cl_15789,cl_63419,cl_42427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_63419 v h) (hints_cons _ _ _ (der_42427 v h) (by intro d hd; cases hd))))
def cl_66487 : CNF.NClause := [(39,false),(114,false),(118,false),(100,false),(105,false),(33,false),(59,false),(108,false),(95,false),(48,false)]
theorem der_66487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66487 :=
  CNF.rup_sound cl_66487 [cl_62370,cl_54086,cl_36748,cl_7954,cl_7939,cl_64221,cl_50221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62370 v h) (hints_cons _ _ _ (der_54086 v h) (hints_cons _ _ _ (der_36748 v h) (hints_cons _ _ _ (inp_7954 v h) (hints_cons _ _ _ (inp_7939 v h) (hints_cons _ _ _ (der_64221 v h) (hints_cons _ _ _ (der_50221 v h) (by intro d hd; cases hd))))))))
def cl_66552 : CNF.NClause := [(107,true),(55,false),(48,false)]
theorem der_66552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66552 :=
  CNF.rup_sound cl_66552 [cl_53764,cl_47910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53764 v h) (hints_cons _ _ _ (der_47910 v h) (by intro d hd; cases hd)))
def cl_66565 : CNF.NClause := [(36,false),(95,false),(106,false),(20,false),(109,false),(68,false),(121,false),(71,false),(85,false),(83,false),(70,false),(69,false),(86,false),(53,false),(67,false)]
theorem der_66565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66565 :=
  CNF.rup_sound cl_66565 [cl_63482,cl_49528,cl_6529,cl_7959,cl_64196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63482 v h) (hints_cons _ _ _ (der_49528 v h) (hints_cons _ _ _ (inp_6529 v h) (hints_cons _ _ _ (inp_7959 v h) (hints_cons _ _ _ (der_64196 v h) (by intro d hd; cases hd))))))
def cl_66589 : CNF.NClause := [(102,true),(44,false),(50,false)]
theorem der_66589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66589 :=
  CNF.rup_sound cl_66589 [cl_54148,cl_62204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54148 v h) (hints_cons _ _ _ (der_62204 v h) (by intro d hd; cases hd)))
def cl_66604 : CNF.NClause := [(153,true),(140,true),(148,true),(152,true),(137,true),(150,true),(132,true),(138,true),(142,true),(139,true),(135,true),(131,true)]
theorem der_66604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66604 :=
  CNF.rup_sound cl_66604 [cl_15619,cl_8081,cl_15663,cl_15631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15619 v h) (hints_cons _ _ _ (inp_8081 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_15631 v h) (by intro d hd; cases hd)))))
def cl_66607 : CNF.NClause := [(73,true),(142,false),(18,false),(7,true)]
theorem der_66607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66607 :=
  CNF.rup_sound cl_66607 [cl_56327,cl_62283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56327 v h) (hints_cons _ _ _ (der_62283 v h) (by intro d hd; cases hd)))
def cl_66609 : CNF.NClause := [(143,false),(50,true),(85,false),(74,false),(15,true),(18,false),(90,false)]
theorem der_66609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66609 :=
  CNF.rup_sound cl_66609 [cl_15785,cl_62594,cl_63480,cl_52792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_62594 v h) (hints_cons _ _ _ (der_63480 v h) (hints_cons _ _ _ (der_52792 v h) (by intro d hd; cases hd)))))
def cl_66628 : CNF.NClause := [(137,false),(71,true)]
theorem der_66628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66628 :=
  CNF.rup_sound cl_66628 [cl_15779,cl_63490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_63490 v h) (by intro d hd; cases hd)))
def cl_66645 : CNF.NClause := [(101,true),(10,false),(150,true),(3,false),(137,false),(71,false),(143,true),(48,false),(80,false),(68,false),(85,false),(65,false),(70,false),(69,false),(131,true),(146,false)]
theorem der_66645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66645 :=
  CNF.rup_sound cl_66645 [cl_63071,cl_62576,cl_50002,cl_50276,cl_49841,cl_66375,cl_58161,cl_15786,cl_15767,cl_8025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_62576 v h) (hints_cons _ _ _ (der_50002 v h) (hints_cons _ _ _ (der_50276 v h) (hints_cons _ _ _ (der_49841 v h) (hints_cons _ _ _ (der_66375 v h) (hints_cons _ _ _ (der_58161 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (inp_8025 v h) (by intro d hd; cases hd)))))))))))
def cl_66646 : CNF.NClause := [(23,false),(101,false),(81,false),(108,false),(119,false),(151,false),(95,false),(48,false),(85,false),(65,false),(74,false),(141,false),(69,false),(11,true),(7,true),(78,false),(67,false)]
theorem der_66646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66646 :=
  CNF.rup_sound cl_66646 [cl_15792,cl_65746,cl_15783,cl_52758,cl_42427,cl_42515,cl_62683,cl_7954,cl_42767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_65746 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_52758 v h) (hints_cons _ _ _ (der_42427 v h) (hints_cons _ _ _ (der_42515 v h) (hints_cons _ _ _ (der_62683 v h) (hints_cons _ _ _ (inp_7954 v h) (hints_cons _ _ _ (der_42767 v h) (by intro d hd; cases hd))))))))))
def cl_66718 : CNF.NClause := [(3,false),(107,false),(119,false),(108,false),(128,false),(95,false),(48,false),(80,false),(85,false),(73,false),(65,false),(83,false),(70,false),(78,false),(75,false)]
theorem der_66718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66718 :=
  CNF.rup_sound cl_66718 [cl_62565,cl_15770,cl_62665,cl_65702,cl_44573,cl_49841,cl_7954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62565 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_62665 v h) (hints_cons _ _ _ (der_65702 v h) (hints_cons _ _ _ (der_44573 v h) (hints_cons _ _ _ (der_49841 v h) (hints_cons _ _ _ (inp_7954 v h) (by intro d hd; cases hd))))))))
def cl_66731 : CNF.NClause := [(23,false),(27,false),(151,false),(109,false),(40,false),(81,false),(60,false),(34,false),(48,false),(85,false),(65,false),(74,false),(141,false),(69,false),(11,true),(7,true),(78,false),(67,false)]
theorem der_66731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66731 :=
  CNF.rup_sound cl_66731 [cl_65746,cl_15783,cl_52758,cl_42427,cl_62683,cl_54984,cl_42515,cl_42810,cl_49933,cl_64264,cl_7964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65746 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_52758 v h) (hints_cons _ _ _ (der_42427 v h) (hints_cons _ _ _ (der_62683 v h) (hints_cons _ _ _ (der_54984 v h) (hints_cons _ _ _ (der_42515 v h) (hints_cons _ _ _ (der_42810 v h) (hints_cons _ _ _ (der_49933 v h) (hints_cons _ _ _ (der_64264 v h) (hints_cons _ _ _ (inp_7964 v h) (by intro d hd; cases hd))))))))))))
def cl_66741 : CNF.NClause := [(151,false),(1,false),(150,false),(108,false),(91,false),(72,false),(79,false),(14,false),(63,false),(143,true),(95,false),(48,false),(88,false),(80,false),(68,false),(29,false),(85,false),(74,false),(76,false),(83,false),(70,false),(69,false),(7,true),(86,false),(78,false),(75,false)]
theorem der_66741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66741 :=
  CNF.rup_sound cl_66741 [cl_15792,cl_42018,cl_49901,cl_42515,cl_56304,cl_65946,cl_50002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_42018 v h) (hints_cons _ _ _ (der_49901 v h) (hints_cons _ _ _ (der_42515 v h) (hints_cons _ _ _ (der_56304 v h) (hints_cons _ _ _ (der_65946 v h) (hints_cons _ _ _ (der_50002 v h) (by intro d hd; cases hd))))))))
def cl_66744 : CNF.NClause := [(126,false),(93,false),(111,false),(119,false),(60,false),(117,false),(79,false),(128,false),(84,false),(73,false),(74,false),(83,false),(69,false),(131,true),(78,false)]
theorem der_66744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66744 :=
  CNF.rup_sound cl_66744 [cl_62565,cl_15770,cl_15768,cl_63359,cl_54172,cl_54056,cl_49975,cl_7966,cl_49984,cl_50332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62565 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_63359 v h) (hints_cons _ _ _ (der_54172 v h) (hints_cons _ _ _ (der_54056 v h) (hints_cons _ _ _ (der_49975 v h) (hints_cons _ _ _ (inp_7966 v h) (hints_cons _ _ _ (der_49984 v h) (hints_cons _ _ _ (der_50332 v h) (by intro d hd; cases hd)))))))))))
def cl_66788 : CNF.NClause := [(23,false),(54,true),(81,false),(27,false),(65,false),(74,false),(17,false),(11,true),(67,false)]
theorem der_66788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66788 :=
  CNF.rup_sound cl_66788 [cl_42427,cl_62683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42427 v h) (hints_cons _ _ _ (der_62683 v h) (by intro d hd; cases hd)))
def cl_66816 : CNF.NClause := [(28,false),(81,true),(919,false),(904,true),(912,true),(926,true),(915,true),(922,true),(917,true),(923,true),(911,true),(15,true),(910,true)]
theorem der_66816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66816 :=
  CNF.rup_sound cl_66816 [cl_15881,cl_61226,cl_50145,cl_15875,cl_15867,cl_12732,cl_12661,cl_12755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_61226 v h) (hints_cons _ _ _ (der_50145 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (inp_12732 v h) (hints_cons _ _ _ (inp_12661 v h) (hints_cons _ _ _ (inp_12755 v h) (by intro d hd; cases hd)))))))))
def cl_66817 : CNF.NClause := [(81,true),(919,false),(904,true),(912,true),(926,true),(915,true),(922,true),(917,true),(923,true),(911,true),(15,true),(910,true)]
theorem der_66817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66817 :=
  CNF.rup_sound cl_66817 [cl_15881,cl_66816,cl_15893,cl_12755,cl_12661,cl_15875,cl_12736,cl_49792,cl_15867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_66816 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (inp_12755 v h) (hints_cons _ _ _ (inp_12661 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (inp_12736 v h) (hints_cons _ _ _ (der_49792 v h) (hints_cons _ _ _ (der_15867 v h) (by intro d hd; cases hd))))))))))
def cl_66828 : CNF.NClause := [(63,true),(241,false),(24,false),(3,true)]
theorem der_66828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66828 :=
  CNF.rup_sound cl_66828 [cl_15802,cl_49833,cl_49999,cl_29919,cl_49874,cl_13859,cl_13869,cl_13864,cl_13874,cl_8533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15802 v h) (hints_cons _ _ _ (der_49833 v h) (hints_cons _ _ _ (der_49999 v h) (hints_cons _ _ _ (der_29919 v h) (hints_cons _ _ _ (der_49874 v h) (hints_cons _ _ _ (inp_13859 v h) (hints_cons _ _ _ (inp_13869 v h) (hints_cons _ _ _ (inp_13864 v h) (hints_cons _ _ _ (inp_13874 v h) (hints_cons _ _ _ (inp_8533 v h) (by intro d hd; cases hd)))))))))))
def cl_66831 : CNF.NClause := [(12,false),(928,true),(923,true),(901,true),(909,true),(919,true),(900,true),(902,true),(915,true),(922,true),(913,true),(81,true),(15,true),(906,true)]
theorem der_66831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66831 :=
  CNF.rup_sound cl_66831 [cl_15881,cl_50136,cl_50137,cl_15893,cl_15875,cl_19574,cl_12735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_50136 v h) (hints_cons _ _ _ (der_50137 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_19574 v h) (hints_cons _ _ _ (inp_12735 v h) (by intro d hd; cases hd))))))))
def cl_66833 : CNF.NClause := [(29,true),(63,true),(232,true),(224,true),(3,true),(480,true),(472,true),(11,true)]
theorem der_66833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66833 :=
  CNF.rup_sound cl_66833 [cl_14099,cl_13866,cl_13738,cl_13746,cl_14124,cl_13884,cl_10125,cl_8639,cl_14119,cl_66828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14099 v h) (hints_cons _ _ _ (inp_13866 v h) (hints_cons _ _ _ (inp_13738 v h) (hints_cons _ _ _ (inp_13746 v h) (hints_cons _ _ _ (inp_14124 v h) (hints_cons _ _ _ (inp_13884 v h) (hints_cons _ _ _ (inp_10125 v h) (hints_cons _ _ _ (inp_8639 v h) (hints_cons _ _ _ (inp_14119 v h) (hints_cons _ _ _ (der_66828 v h) (by intro d hd; cases hd)))))))))))
def cl_66834 : CNF.NClause := [(923,true),(901,true),(909,true),(919,true),(900,true),(902,true),(915,true),(922,true),(913,true),(81,true),(15,true),(910,true),(906,true)]
theorem der_66834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66834 :=
  CNF.rup_sound cl_66834 [cl_15881,cl_12726,cl_66831,cl_15878,cl_19574,cl_15893,cl_12732,cl_61226,cl_15875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (inp_12726 v h) (hints_cons _ _ _ (der_66831 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_19574 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (inp_12732 v h) (hints_cons _ _ _ (der_61226 v h) (hints_cons _ _ _ (der_15875 v h) (by intro d hd; cases hd))))))))))
def cl_66845 : CNF.NClause := [(34,true),(127,true),(3,false),(80,false),(128,true),(85,false),(65,false),(70,false),(75,false)]
theorem der_66845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66845 :=
  CNF.rup_sound cl_66845 [cl_58338,cl_58161,cl_15768,cl_15767,cl_15661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58338 v h) (hints_cons _ _ _ (der_58161 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_15661 v h) (by intro d hd; cases hd))))))
def cl_66884 : CNF.NClause := [(137,false),(44,true),(71,false),(88,false),(84,false),(65,false),(78,false)]
theorem der_66884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66884 :=
  CNF.rup_sound cl_66884 [cl_15779,cl_62596,cl_5633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_62596 v h) (hints_cons _ _ _ (inp_5633 v h) (by intro d hd; cases hd))))
def cl_66890 : CNF.NClause := [(72,false),(10,true),(14,true),(43,true),(68,false),(81,false),(91,false),(85,false),(11,true),(64,false)]
theorem der_66890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66890 :=
  CNF.rup_sound cl_66890 [cl_5505,cl_29823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5505 v h) (hints_cons _ _ _ (der_29823 v h) (by intro d hd; cases hd)))
def cl_66900 : CNF.NClause := [(130,true),(123,false),(107,false),(104,false),(106,false),(41,false),(125,false),(126,true),(134,false),(145,true),(71,false),(81,false),(143,true),(88,false),(128,true),(151,true),(153,true),(84,false),(65,false),(74,false),(17,false),(139,true),(11,true),(78,false),(146,false)]
theorem der_66900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66900 :=
  CNF.rup_sound cl_66900 [cl_15777,cl_63071,cl_8065,cl_8043,cl_15640,cl_66884,cl_15789,cl_15782,cl_64459,cl_49762,cl_7947,cl_62683,cl_50016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (inp_8065 v h) (hints_cons _ _ _ (inp_8043 v h) (hints_cons _ _ _ (der_15640 v h) (hints_cons _ _ _ (der_66884 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_64459 v h) (hints_cons _ _ _ (der_49762 v h) (hints_cons _ _ _ (inp_7947 v h) (hints_cons _ _ _ (der_62683 v h) (hints_cons _ _ _ (der_50016 v h) (by intro d hd; cases hd))))))))))))))
def cl_66914 : CNF.NClause := [(54,false),(81,true),(65,false),(74,false),(83,false),(67,false)]
theorem der_66914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_66914 :=
  CNF.rup_sound cl_66914 [cl_32542,cl_52254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32542 v h) (hints_cons _ _ _ (der_52254 v h) (by intro d hd; cases hd)))
def chunk061 : List CNF.NClause := [cl_62315,cl_62316,cl_62317,cl_62318,cl_62319,cl_62321,cl_62322,cl_62323,cl_62324,cl_62332,cl_62333,cl_62338,cl_62339,cl_62340,cl_62349,cl_62353,cl_62355,cl_62357,cl_62365,cl_62370,cl_62389,cl_62391,cl_62393,cl_62396,cl_62402,cl_62405,cl_62409,cl_62411,cl_62414,cl_62416,cl_62424,cl_62431,cl_62447,cl_62452,cl_62455,cl_62461,cl_62463,cl_62466,cl_62474,cl_62484,cl_62489,cl_62507,cl_62510,cl_62559,cl_62560,cl_62561,cl_62562,cl_62563,cl_62564,cl_62565,cl_62566,cl_62569,cl_62571,cl_62572,cl_62573,cl_62574,cl_62575,cl_62576,cl_62577,cl_62580,cl_62584,cl_62587,cl_62589,cl_62591,cl_62592,cl_62594,cl_62595,cl_62596,cl_62606,cl_62618,cl_62627,cl_62639,cl_62641,cl_62665,cl_62670,cl_62672,cl_62677,cl_62678,cl_62682,cl_62683,cl_62684,cl_62690,cl_62696,cl_62702,cl_62705,cl_62741,cl_62747,cl_62752,cl_62787,cl_62789,cl_62806,cl_62836,cl_62857,cl_62871,cl_62873,cl_62886,cl_62898,cl_62905,cl_62910,cl_62911,cl_62914,cl_62926,cl_62957,cl_62965,cl_62974,cl_62981,cl_62986,cl_62991,cl_63010,cl_63026,cl_63027,cl_63039,cl_63040,cl_63041,cl_63052,cl_63068,cl_63071,cl_63080,cl_63081,cl_63096,cl_63163,cl_63179,cl_63185,cl_63192,cl_63197,cl_63208,cl_63248,cl_63255,cl_63328,cl_63356,cl_63359,cl_63367,cl_63372,cl_63385,cl_63400,cl_63405,cl_63419,cl_63439,cl_63458,cl_63459,cl_63461,cl_63464,cl_63466,cl_63467,cl_63479,cl_63480,cl_63482,cl_63490,cl_63501,cl_63502,cl_63516,cl_63517,cl_63525,cl_63531,cl_63532,cl_63559,cl_63561,cl_63563,cl_63577,cl_63581,cl_63584,cl_63585,cl_63594,cl_63604,cl_63620,cl_63622,cl_63629,cl_63631,cl_63645,cl_63651,cl_63662,cl_63665,cl_63667,cl_63674,cl_63714,cl_63743,cl_63746,cl_63749,cl_63752,cl_63753,cl_63761,cl_63771,cl_63775,cl_63793,cl_63795,cl_63802,cl_63840,cl_63850,cl_63872,cl_63882,cl_63895,cl_63921,cl_63928,cl_63950,cl_63952,cl_63957,cl_63960,cl_63963,cl_63986,cl_64006,cl_64012,cl_64022,cl_64028,cl_64034,cl_64042,cl_64050,cl_64053,cl_64065,cl_64072,cl_64082,cl_64097,cl_64098,cl_64103,cl_64104,cl_64105,cl_64106,cl_64107,cl_64108,cl_64109,cl_64111,cl_64113,cl_64115,cl_64116,cl_64117,cl_64118,cl_64120,cl_64121,cl_64122,cl_64123,cl_64125,cl_64126,cl_64127,cl_64130,cl_64131,cl_64132,cl_64134,cl_64135,cl_64136,cl_64137,cl_64138,cl_64139,cl_64141,cl_64142,cl_64143,cl_64144,cl_64145,cl_64146,cl_64147,cl_64148,cl_64149,cl_64150,cl_64151,cl_64152,cl_64153,cl_64154,cl_64155,cl_64156,cl_64157,cl_64158,cl_64159,cl_64162,cl_64163,cl_64164,cl_64165,cl_64166,cl_64167,cl_64168,cl_64169,cl_64170,cl_64171,cl_64172,cl_64173,cl_64175,cl_64176,cl_64178,cl_64179,cl_64180,cl_64182,cl_64183,cl_64184,cl_64185,cl_64186,cl_64187,cl_64190,cl_64191,cl_64192,cl_64195,cl_64196,cl_64197,cl_64198,cl_64199,cl_64202,cl_64204,cl_64205,cl_64206,cl_64207,cl_64209,cl_64210,cl_64213,cl_64214,cl_64215,cl_64216,cl_64217,cl_64219,cl_64220,cl_64221,cl_64223,cl_64224,cl_64225,cl_64227,cl_64229,cl_64233,cl_64235,cl_64258,cl_64261,cl_64264,cl_64269,cl_64270,cl_64271,cl_64275,cl_64277,cl_64278,cl_64279,cl_64281,cl_64282,cl_64284,cl_64285,cl_64291,cl_64296,cl_64302,cl_64303,cl_64307,cl_64310,cl_64311,cl_64320,cl_64327,cl_64332,cl_64335,cl_64336,cl_64337,cl_64338,cl_64341,cl_64344,cl_64345,cl_64346,cl_64348,cl_64351,cl_64358,cl_64359,cl_64365,cl_64372,cl_64373,cl_64374,cl_64377,cl_64378,cl_64381,cl_64459,cl_64460,cl_64488,cl_64558,cl_64560,cl_64596,cl_64694,cl_64722,cl_64745,cl_64752,cl_64780,cl_64857,cl_64888,cl_64952,cl_64956,cl_64958,cl_65025,cl_65062,cl_65072,cl_65073,cl_65112,cl_65113,cl_65120,cl_65218,cl_65385,cl_65409,cl_65425,cl_65428,cl_65458,cl_65470,cl_65480,cl_65500,cl_65550,cl_65554,cl_65562,cl_65566,cl_65568,cl_65588,cl_65604,cl_65616,cl_65618,cl_65619,cl_65638,cl_65642,cl_65647,cl_65676,cl_65682,cl_65683,cl_65687,cl_65690,cl_65696,cl_65699,cl_65702,cl_65706,cl_65712,cl_65714,cl_65716,cl_65720,cl_65724,cl_65725,cl_65727,cl_65736,cl_65737,cl_65738,cl_65746,cl_65751,cl_65753,cl_65759,cl_65773,cl_65774,cl_65781,cl_65811,cl_65820,cl_65835,cl_65849,cl_65850,cl_65851,cl_65857,cl_65861,cl_65888,cl_65889,cl_65890,cl_65896,cl_65899,cl_65909,cl_65919,cl_65937,cl_65946,cl_65951,cl_65980,cl_65997,cl_66000,cl_66003,cl_66025,cl_66045,cl_66105,cl_66108,cl_66126,cl_66131,cl_66156,cl_66178,cl_66186,cl_66199,cl_66231,cl_66240,cl_66321,cl_66359,cl_66372,cl_66375,cl_66383,cl_66388,cl_66405,cl_66455,cl_66469,cl_66472,cl_66477,cl_66480,cl_66483,cl_66487,cl_66552,cl_66565,cl_66589,cl_66604,cl_66607,cl_66609,cl_66628,cl_66645,cl_66646,cl_66718,cl_66731,cl_66741,cl_66744,cl_66788,cl_66816,cl_66817,cl_66828,cl_66831,cl_66833,cl_66834,cl_66845,cl_66884,cl_66890,cl_66900,cl_66914]
theorem chunk_sound061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk061, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_62315 v h) (hints_cons _ _ _ (der_62316 v h) (hints_cons _ _ _ (der_62317 v h) (hints_cons _ _ _ (der_62318 v h) (hints_cons _ _ _ (der_62319 v h) (hints_cons _ _ _ (der_62321 v h) (hints_cons _ _ _ (der_62322 v h) (hints_cons _ _ _ (der_62323 v h) (hints_cons _ _ _ (der_62324 v h) (hints_cons _ _ _ (der_62332 v h) (hints_cons _ _ _ (der_62333 v h) (hints_cons _ _ _ (der_62338 v h) (hints_cons _ _ _ (der_62339 v h) (hints_cons _ _ _ (der_62340 v h) (hints_cons _ _ _ (der_62349 v h) (hints_cons _ _ _ (der_62353 v h) (hints_cons _ _ _ (der_62355 v h) (hints_cons _ _ _ (der_62357 v h) (hints_cons _ _ _ (der_62365 v h) (hints_cons _ _ _ (der_62370 v h) (hints_cons _ _ _ (der_62389 v h) (hints_cons _ _ _ (der_62391 v h) (hints_cons _ _ _ (der_62393 v h) (hints_cons _ _ _ (der_62396 v h) (hints_cons _ _ _ (der_62402 v h) (hints_cons _ _ _ (der_62405 v h) (hints_cons _ _ _ (der_62409 v h) (hints_cons _ _ _ (der_62411 v h) (hints_cons _ _ _ (der_62414 v h) (hints_cons _ _ _ (der_62416 v h) (hints_cons _ _ _ (der_62424 v h) (hints_cons _ _ _ (der_62431 v h) (hints_cons _ _ _ (der_62447 v h) (hints_cons _ _ _ (der_62452 v h) (hints_cons _ _ _ (der_62455 v h) (hints_cons _ _ _ (der_62461 v h) (hints_cons _ _ _ (der_62463 v h) (hints_cons _ _ _ (der_62466 v h) (hints_cons _ _ _ (der_62474 v h) (hints_cons _ _ _ (der_62484 v h) (hints_cons _ _ _ (der_62489 v h) (hints_cons _ _ _ (der_62507 v h) (hints_cons _ _ _ (der_62510 v h) (hints_cons _ _ _ (der_62559 v h) (hints_cons _ _ _ (der_62560 v h) (hints_cons _ _ _ (der_62561 v h) (hints_cons _ _ _ (der_62562 v h) (hints_cons _ _ _ (der_62563 v h) (hints_cons _ _ _ (der_62564 v h) (hints_cons _ _ _ (der_62565 v h) (hints_cons _ _ _ (der_62566 v h) (hints_cons _ _ _ (der_62569 v h) (hints_cons _ _ _ (der_62571 v h) (hints_cons _ _ _ (der_62572 v h) (hints_cons _ _ _ (der_62573 v h) (hints_cons _ _ _ (der_62574 v h) (hints_cons _ _ _ (der_62575 v h) (hints_cons _ _ _ (der_62576 v h) (hints_cons _ _ _ (der_62577 v h) (hints_cons _ _ _ (der_62580 v h) (hints_cons _ _ _ (der_62584 v h) (hints_cons _ _ _ (der_62587 v h) (hints_cons _ _ _ (der_62589 v h) (hints_cons _ _ _ (der_62591 v h) (hints_cons _ _ _ (der_62592 v h) (hints_cons _ _ _ (der_62594 v h) (hints_cons _ _ _ (der_62595 v h) (hints_cons _ _ _ (der_62596 v h) (hints_cons _ _ _ (der_62606 v h) (hints_cons _ _ _ (der_62618 v h) (hints_cons _ _ _ (der_62627 v h) (hints_cons _ _ _ (der_62639 v h) (hints_cons _ _ _ (der_62641 v h) (hints_cons _ _ _ (der_62665 v h) (hints_cons _ _ _ (der_62670 v h) (hints_cons _ _ _ (der_62672 v h) (hints_cons _ _ _ (der_62677 v h) (hints_cons _ _ _ (der_62678 v h) (hints_cons _ _ _ (der_62682 v h) (hints_cons _ _ _ (der_62683 v h) (hints_cons _ _ _ (der_62684 v h) (hints_cons _ _ _ (der_62690 v h) (hints_cons _ _ _ (der_62696 v h) (hints_cons _ _ _ (der_62702 v h) (hints_cons _ _ _ (der_62705 v h) (hints_cons _ _ _ (der_62741 v h) (hints_cons _ _ _ (der_62747 v h) (hints_cons _ _ _ (der_62752 v h) (hints_cons _ _ _ (der_62787 v h) (hints_cons _ _ _ (der_62789 v h) (hints_cons _ _ _ (der_62806 v h) (hints_cons _ _ _ (der_62836 v h) (hints_cons _ _ _ (der_62857 v h) (hints_cons _ _ _ (der_62871 v h) (hints_cons _ _ _ (der_62873 v h) (hints_cons _ _ _ (der_62886 v h) (hints_cons _ _ _ (der_62898 v h) (hints_cons _ _ _ (der_62905 v h) (hints_cons _ _ _ (der_62910 v h) (hints_cons _ _ _ (der_62911 v h) (hints_cons _ _ _ (der_62914 v h) (hints_cons _ _ _ (der_62926 v h) (hints_cons _ _ _ (der_62957 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_62974 v h) (hints_cons _ _ _ (der_62981 v h) (hints_cons _ _ _ (der_62986 v h) (hints_cons _ _ _ (der_62991 v h) (hints_cons _ _ _ (der_63010 v h) (hints_cons _ _ _ (der_63026 v h) (hints_cons _ _ _ (der_63027 v h) (hints_cons _ _ _ (der_63039 v h) (hints_cons _ _ _ (der_63040 v h) (hints_cons _ _ _ (der_63041 v h) (hints_cons _ _ _ (der_63052 v h) (hints_cons _ _ _ (der_63068 v h) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_63080 v h) (hints_cons _ _ _ (der_63081 v h) (hints_cons _ _ _ (der_63096 v h) (hints_cons _ _ _ (der_63163 v h) (hints_cons _ _ _ (der_63179 v h) (hints_cons _ _ _ (der_63185 v h) (hints_cons _ _ _ (der_63192 v h) (hints_cons _ _ _ (der_63197 v h) (hints_cons _ _ _ (der_63208 v h) (hints_cons _ _ _ (der_63248 v h) (hints_cons _ _ _ (der_63255 v h) (hints_cons _ _ _ (der_63328 v h) (hints_cons _ _ _ (der_63356 v h) (hints_cons _ _ _ (der_63359 v h) (hints_cons _ _ _ (der_63367 v h) (hints_cons _ _ _ (der_63372 v h) (hints_cons _ _ _ (der_63385 v h) (hints_cons _ _ _ (der_63400 v h) (hints_cons _ _ _ (der_63405 v h) (hints_cons _ _ _ (der_63419 v h) (hints_cons _ _ _ (der_63439 v h) (hints_cons _ _ _ (der_63458 v h) (hints_cons _ _ _ (der_63459 v h) (hints_cons _ _ _ (der_63461 v h) (hints_cons _ _ _ (der_63464 v h) (hints_cons _ _ _ (der_63466 v h) (hints_cons _ _ _ (der_63467 v h) (hints_cons _ _ _ (der_63479 v h) (hints_cons _ _ _ (der_63480 v h) (hints_cons _ _ _ (der_63482 v h) (hints_cons _ _ _ (der_63490 v h) (hints_cons _ _ _ (der_63501 v h) (hints_cons _ _ _ (der_63502 v h) (hints_cons _ _ _ (der_63516 v h) (hints_cons _ _ _ (der_63517 v h) (hints_cons _ _ _ (der_63525 v h) (hints_cons _ _ _ (der_63531 v h) (hints_cons _ _ _ (der_63532 v h) (hints_cons _ _ _ (der_63559 v h) (hints_cons _ _ _ (der_63561 v h) (hints_cons _ _ _ (der_63563 v h) (hints_cons _ _ _ (der_63577 v h) (hints_cons _ _ _ (der_63581 v h) (hints_cons _ _ _ (der_63584 v h) (hints_cons _ _ _ (der_63585 v h) (hints_cons _ _ _ (der_63594 v h) (hints_cons _ _ _ (der_63604 v h) (hints_cons _ _ _ (der_63620 v h) (hints_cons _ _ _ (der_63622 v h) (hints_cons _ _ _ (der_63629 v h) (hints_cons _ _ _ (der_63631 v h) (hints_cons _ _ _ (der_63645 v h) (hints_cons _ _ _ (der_63651 v h) (hints_cons _ _ _ (der_63662 v h) (hints_cons _ _ _ (der_63665 v h) (hints_cons _ _ _ (der_63667 v h) (hints_cons _ _ _ (der_63674 v h) (hints_cons _ _ _ (der_63714 v h) (hints_cons _ _ _ (der_63743 v h) (hints_cons _ _ _ (der_63746 v h) (hints_cons _ _ _ (der_63749 v h) (hints_cons _ _ _ (der_63752 v h) (hints_cons _ _ _ (der_63753 v h) (hints_cons _ _ _ (der_63761 v h) (hints_cons _ _ _ (der_63771 v h) (hints_cons _ _ _ (der_63775 v h) (hints_cons _ _ _ (der_63793 v h) (hints_cons _ _ _ (der_63795 v h) (hints_cons _ _ _ (der_63802 v h) (hints_cons _ _ _ (der_63840 v h) (hints_cons _ _ _ (der_63850 v h) (hints_cons _ _ _ (der_63872 v h) (hints_cons _ _ _ (der_63882 v h) (hints_cons _ _ _ (der_63895 v h) (hints_cons _ _ _ (der_63921 v h) (hints_cons _ _ _ (der_63928 v h) (hints_cons _ _ _ (der_63950 v h) (hints_cons _ _ _ (der_63952 v h) (hints_cons _ _ _ (der_63957 v h) (hints_cons _ _ _ (der_63960 v h) (hints_cons _ _ _ (der_63963 v h) (hints_cons _ _ _ (der_63986 v h) (hints_cons _ _ _ (der_64006 v h) (hints_cons _ _ _ (der_64012 v h) (hints_cons _ _ _ (der_64022 v h) (hints_cons _ _ _ (der_64028 v h) (hints_cons _ _ _ (der_64034 v h) (hints_cons _ _ _ (der_64042 v h) (hints_cons _ _ _ (der_64050 v h) (hints_cons _ _ _ (der_64053 v h) (hints_cons _ _ _ (der_64065 v h) (hints_cons _ _ _ (der_64072 v h) (hints_cons _ _ _ (der_64082 v h) (hints_cons _ _ _ (der_64097 v h) (hints_cons _ _ _ (der_64098 v h) (hints_cons _ _ _ (der_64103 v h) (hints_cons _ _ _ (der_64104 v h) (hints_cons _ _ _ (der_64105 v h) (hints_cons _ _ _ (der_64106 v h) (hints_cons _ _ _ (der_64107 v h) (hints_cons _ _ _ (der_64108 v h) (hints_cons _ _ _ (der_64109 v h) (hints_cons _ _ _ (der_64111 v h) (hints_cons _ _ _ (der_64113 v h) (hints_cons _ _ _ (der_64115 v h) (hints_cons _ _ _ (der_64116 v h) (hints_cons _ _ _ (der_64117 v h) (hints_cons _ _ _ (der_64118 v h) (hints_cons _ _ _ (der_64120 v h) (hints_cons _ _ _ (der_64121 v h) (hints_cons _ _ _ (der_64122 v h) (hints_cons _ _ _ (der_64123 v h) (hints_cons _ _ _ (der_64125 v h) (hints_cons _ _ _ (der_64126 v h) (hints_cons _ _ _ (der_64127 v h) (hints_cons _ _ _ (der_64130 v h) (hints_cons _ _ _ (der_64131 v h) (hints_cons _ _ _ (der_64132 v h) (hints_cons _ _ _ (der_64134 v h) (hints_cons _ _ _ (der_64135 v h) (hints_cons _ _ _ (der_64136 v h) (hints_cons _ _ _ (der_64137 v h) (hints_cons _ _ _ (der_64138 v h) (hints_cons _ _ _ (der_64139 v h) (hints_cons _ _ _ (der_64141 v h) (hints_cons _ _ _ (der_64142 v h) (hints_cons _ _ _ (der_64143 v h) (hints_cons _ _ _ (der_64144 v h) (hints_cons _ _ _ (der_64145 v h) (hints_cons _ _ _ (der_64146 v h) (hints_cons _ _ _ (der_64147 v h) (hints_cons _ _ _ (der_64148 v h) (hints_cons _ _ _ (der_64149 v h) (hints_cons _ _ _ (der_64150 v h) (hints_cons _ _ _ (der_64151 v h) (hints_cons _ _ _ (der_64152 v h) (hints_cons _ _ _ (der_64153 v h) (hints_cons _ _ _ (der_64154 v h) (hints_cons _ _ _ (der_64155 v h) (hints_cons _ _ _ (der_64156 v h) (hints_cons _ _ _ (der_64157 v h) (hints_cons _ _ _ (der_64158 v h) (hints_cons _ _ _ (der_64159 v h) (hints_cons _ _ _ (der_64162 v h) (hints_cons _ _ _ (der_64163 v h) (hints_cons _ _ _ (der_64164 v h) (hints_cons _ _ _ (der_64165 v h) (hints_cons _ _ _ (der_64166 v h) (hints_cons _ _ _ (der_64167 v h) (hints_cons _ _ _ (der_64168 v h) (hints_cons _ _ _ (der_64169 v h) (hints_cons _ _ _ (der_64170 v h) (hints_cons _ _ _ (der_64171 v h) (hints_cons _ _ _ (der_64172 v h) (hints_cons _ _ _ (der_64173 v h) (hints_cons _ _ _ (der_64175 v h) (hints_cons _ _ _ (der_64176 v h) (hints_cons _ _ _ (der_64178 v h) (hints_cons _ _ _ (der_64179 v h) (hints_cons _ _ _ (der_64180 v h) (hints_cons _ _ _ (der_64182 v h) (hints_cons _ _ _ (der_64183 v h) (hints_cons _ _ _ (der_64184 v h) (hints_cons _ _ _ (der_64185 v h) (hints_cons _ _ _ (der_64186 v h) (hints_cons _ _ _ (der_64187 v h) (hints_cons _ _ _ (der_64190 v h) (hints_cons _ _ _ (der_64191 v h) (hints_cons _ _ _ (der_64192 v h) (hints_cons _ _ _ (der_64195 v h) (hints_cons _ _ _ (der_64196 v h) (hints_cons _ _ _ (der_64197 v h) (hints_cons _ _ _ (der_64198 v h) (hints_cons _ _ _ (der_64199 v h) (hints_cons _ _ _ (der_64202 v h) (hints_cons _ _ _ (der_64204 v h) (hints_cons _ _ _ (der_64205 v h) (hints_cons _ _ _ (der_64206 v h) (hints_cons _ _ _ (der_64207 v h) (hints_cons _ _ _ (der_64209 v h) (hints_cons _ _ _ (der_64210 v h) (hints_cons _ _ _ (der_64213 v h) (hints_cons _ _ _ (der_64214 v h) (hints_cons _ _ _ (der_64215 v h) (hints_cons _ _ _ (der_64216 v h) (hints_cons _ _ _ (der_64217 v h) (hints_cons _ _ _ (der_64219 v h) (hints_cons _ _ _ (der_64220 v h) (hints_cons _ _ _ (der_64221 v h) (hints_cons _ _ _ (der_64223 v h) (hints_cons _ _ _ (der_64224 v h) (hints_cons _ _ _ (der_64225 v h) (hints_cons _ _ _ (der_64227 v h) (hints_cons _ _ _ (der_64229 v h) (hints_cons _ _ _ (der_64233 v h) (hints_cons _ _ _ (der_64235 v h) (hints_cons _ _ _ (der_64258 v h) (hints_cons _ _ _ (der_64261 v h) (hints_cons _ _ _ (der_64264 v h) (hints_cons _ _ _ (der_64269 v h) (hints_cons _ _ _ (der_64270 v h) (hints_cons _ _ _ (der_64271 v h) (hints_cons _ _ _ (der_64275 v h) (hints_cons _ _ _ (der_64277 v h) (hints_cons _ _ _ (der_64278 v h) (hints_cons _ _ _ (der_64279 v h) (hints_cons _ _ _ (der_64281 v h) (hints_cons _ _ _ (der_64282 v h) (hints_cons _ _ _ (der_64284 v h) (hints_cons _ _ _ (der_64285 v h) (hints_cons _ _ _ (der_64291 v h) (hints_cons _ _ _ (der_64296 v h) (hints_cons _ _ _ (der_64302 v h) (hints_cons _ _ _ (der_64303 v h) (hints_cons _ _ _ (der_64307 v h) (hints_cons _ _ _ (der_64310 v h) (hints_cons _ _ _ (der_64311 v h) (hints_cons _ _ _ (der_64320 v h) (hints_cons _ _ _ (der_64327 v h) (hints_cons _ _ _ (der_64332 v h) (hints_cons _ _ _ (der_64335 v h) (hints_cons _ _ _ (der_64336 v h) (hints_cons _ _ _ (der_64337 v h) (hints_cons _ _ _ (der_64338 v h) (hints_cons _ _ _ (der_64341 v h) (hints_cons _ _ _ (der_64344 v h) (hints_cons _ _ _ (der_64345 v h) (hints_cons _ _ _ (der_64346 v h) (hints_cons _ _ _ (der_64348 v h) (hints_cons _ _ _ (der_64351 v h) (hints_cons _ _ _ (der_64358 v h) (hints_cons _ _ _ (der_64359 v h) (hints_cons _ _ _ (der_64365 v h) (hints_cons _ _ _ (der_64372 v h) (hints_cons _ _ _ (der_64373 v h) (hints_cons _ _ _ (der_64374 v h) (hints_cons _ _ _ (der_64377 v h) (hints_cons _ _ _ (der_64378 v h) (hints_cons _ _ _ (der_64381 v h) (hints_cons _ _ _ (der_64459 v h) (hints_cons _ _ _ (der_64460 v h) (hints_cons _ _ _ (der_64488 v h) (hints_cons _ _ _ (der_64558 v h) (hints_cons _ _ _ (der_64560 v h) (hints_cons _ _ _ (der_64596 v h) (hints_cons _ _ _ (der_64694 v h) (hints_cons _ _ _ (der_64722 v h) (hints_cons _ _ _ (der_64745 v h) (hints_cons _ _ _ (der_64752 v h) (hints_cons _ _ _ (der_64780 v h) (hints_cons _ _ _ (der_64857 v h) (hints_cons _ _ _ (der_64888 v h) (hints_cons _ _ _ (der_64952 v h) (hints_cons _ _ _ (der_64956 v h) (hints_cons _ _ _ (der_64958 v h) (hints_cons _ _ _ (der_65025 v h) (hints_cons _ _ _ (der_65062 v h) (hints_cons _ _ _ (der_65072 v h) (hints_cons _ _ _ (der_65073 v h) (hints_cons _ _ _ (der_65112 v h) (hints_cons _ _ _ (der_65113 v h) (hints_cons _ _ _ (der_65120 v h) (hints_cons _ _ _ (der_65218 v h) (hints_cons _ _ _ (der_65385 v h) (hints_cons _ _ _ (der_65409 v h) (hints_cons _ _ _ (der_65425 v h) (hints_cons _ _ _ (der_65428 v h) (hints_cons _ _ _ (der_65458 v h) (hints_cons _ _ _ (der_65470 v h) (hints_cons _ _ _ (der_65480 v h) (hints_cons _ _ _ (der_65500 v h) (hints_cons _ _ _ (der_65550 v h) (hints_cons _ _ _ (der_65554 v h) (hints_cons _ _ _ (der_65562 v h) (hints_cons _ _ _ (der_65566 v h) (hints_cons _ _ _ (der_65568 v h) (hints_cons _ _ _ (der_65588 v h) (hints_cons _ _ _ (der_65604 v h) (hints_cons _ _ _ (der_65616 v h) (hints_cons _ _ _ (der_65618 v h) (hints_cons _ _ _ (der_65619 v h) (hints_cons _ _ _ (der_65638 v h) (hints_cons _ _ _ (der_65642 v h) (hints_cons _ _ _ (der_65647 v h) (hints_cons _ _ _ (der_65676 v h) (hints_cons _ _ _ (der_65682 v h) (hints_cons _ _ _ (der_65683 v h) (hints_cons _ _ _ (der_65687 v h) (hints_cons _ _ _ (der_65690 v h) (hints_cons _ _ _ (der_65696 v h) (hints_cons _ _ _ (der_65699 v h) (hints_cons _ _ _ (der_65702 v h) (hints_cons _ _ _ (der_65706 v h) (hints_cons _ _ _ (der_65712 v h) (hints_cons _ _ _ (der_65714 v h) (hints_cons _ _ _ (der_65716 v h) (hints_cons _ _ _ (der_65720 v h) (hints_cons _ _ _ (der_65724 v h) (hints_cons _ _ _ (der_65725 v h) (hints_cons _ _ _ (der_65727 v h) (hints_cons _ _ _ (der_65736 v h) (hints_cons _ _ _ (der_65737 v h) (hints_cons _ _ _ (der_65738 v h) (hints_cons _ _ _ (der_65746 v h) (hints_cons _ _ _ (der_65751 v h) (hints_cons _ _ _ (der_65753 v h) (hints_cons _ _ _ (der_65759 v h) (hints_cons _ _ _ (der_65773 v h) (hints_cons _ _ _ (der_65774 v h) (hints_cons _ _ _ (der_65781 v h) (hints_cons _ _ _ (der_65811 v h) (hints_cons _ _ _ (der_65820 v h) (hints_cons _ _ _ (der_65835 v h) (hints_cons _ _ _ (der_65849 v h) (hints_cons _ _ _ (der_65850 v h) (hints_cons _ _ _ (der_65851 v h) (hints_cons _ _ _ (der_65857 v h) (hints_cons _ _ _ (der_65861 v h) (hints_cons _ _ _ (der_65888 v h) (hints_cons _ _ _ (der_65889 v h) (hints_cons _ _ _ (der_65890 v h) (hints_cons _ _ _ (der_65896 v h) (hints_cons _ _ _ (der_65899 v h) (hints_cons _ _ _ (der_65909 v h) (hints_cons _ _ _ (der_65919 v h) (hints_cons _ _ _ (der_65937 v h) (hints_cons _ _ _ (der_65946 v h) (hints_cons _ _ _ (der_65951 v h) (hints_cons _ _ _ (der_65980 v h) (hints_cons _ _ _ (der_65997 v h) (hints_cons _ _ _ (der_66000 v h) (hints_cons _ _ _ (der_66003 v h) (hints_cons _ _ _ (der_66025 v h) (hints_cons _ _ _ (der_66045 v h) (hints_cons _ _ _ (der_66105 v h) (hints_cons _ _ _ (der_66108 v h) (hints_cons _ _ _ (der_66126 v h) (hints_cons _ _ _ (der_66131 v h) (hints_cons _ _ _ (der_66156 v h) (hints_cons _ _ _ (der_66178 v h) (hints_cons _ _ _ (der_66186 v h) (hints_cons _ _ _ (der_66199 v h) (hints_cons _ _ _ (der_66231 v h) (hints_cons _ _ _ (der_66240 v h) (hints_cons _ _ _ (der_66321 v h) (hints_cons _ _ _ (der_66359 v h) (hints_cons _ _ _ (der_66372 v h) (hints_cons _ _ _ (der_66375 v h) (hints_cons _ _ _ (der_66383 v h) (hints_cons _ _ _ (der_66388 v h) (hints_cons _ _ _ (der_66405 v h) (hints_cons _ _ _ (der_66455 v h) (hints_cons _ _ _ (der_66469 v h) (hints_cons _ _ _ (der_66472 v h) (hints_cons _ _ _ (der_66477 v h) (hints_cons _ _ _ (der_66480 v h) (hints_cons _ _ _ (der_66483 v h) (hints_cons _ _ _ (der_66487 v h) (hints_cons _ _ _ (der_66552 v h) (hints_cons _ _ _ (der_66565 v h) (hints_cons _ _ _ (der_66589 v h) (hints_cons _ _ _ (der_66604 v h) (hints_cons _ _ _ (der_66607 v h) (hints_cons _ _ _ (der_66609 v h) (hints_cons _ _ _ (der_66628 v h) (hints_cons _ _ _ (der_66645 v h) (hints_cons _ _ _ (der_66646 v h) (hints_cons _ _ _ (der_66718 v h) (hints_cons _ _ _ (der_66731 v h) (hints_cons _ _ _ (der_66741 v h) (hints_cons _ _ _ (der_66744 v h) (hints_cons _ _ _ (der_66788 v h) (hints_cons _ _ _ (der_66816 v h) (hints_cons _ _ _ (der_66817 v h) (hints_cons _ _ _ (der_66828 v h) (hints_cons _ _ _ (der_66831 v h) (hints_cons _ _ _ (der_66833 v h) (hints_cons _ _ _ (der_66834 v h) (hints_cons _ _ _ (der_66845 v h) (hints_cons _ _ _ (der_66884 v h) (hints_cons _ _ _ (der_66890 v h) (hints_cons _ _ _ (der_66900 v h) (hints_cons _ _ _ (der_66914 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix061 := prefix060 ++ chunk061
theorem prefix_sound061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix061, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound060 v h c hc
  · exact chunk_sound061 v h c hc
end Percolation.NReplay
