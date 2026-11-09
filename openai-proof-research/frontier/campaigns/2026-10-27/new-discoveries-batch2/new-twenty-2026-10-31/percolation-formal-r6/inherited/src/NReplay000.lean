import NInputs225
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14699 : CNF.NClause := [(124,true)]
theorem der_14699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14699 :=
  CNF.rup_sound cl_14699 [cl_14696,cl_13735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13735 v h) (by intro d hd; cases hd)))
def cl_14700 : CNF.NClause := [(924,true)]
theorem der_14700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14700 :=
  CNF.rup_sound cl_14700 [cl_14697,cl_13760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_13760 v h) (by intro d hd; cases hd)))
def cl_14701 : CNF.NClause := [(149,false)]
theorem der_14701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14701 :=
  CNF.rup_sound cl_14701 [cl_14697,cl_14696,cl_13790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13790 v h) (by intro d hd; cases hd))))
def cl_14702 : CNF.NClause := [(899,false)]
theorem der_14702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14702 :=
  CNF.rup_sound cl_14702 [cl_14697,cl_14696,cl_14516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14516 v h) (by intro d hd; cases hd))))
def cl_14703 : CNF.NClause := [(1084,true)]
theorem der_14703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14703 :=
  CNF.rup_sound cl_14703 [cl_14698,cl_13765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_13765 v h) (by intro d hd; cases hd)))
def cl_14704 : CNF.NClause := [(154,false)]
theorem der_14704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14704 :=
  CNF.rup_sound cl_14704 [cl_14698,cl_14696,cl_13795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_13795 v h) (by intro d hd; cases hd))))
def cl_14705 : CNF.NClause := [(929,false)]
theorem der_14705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14705 :=
  CNF.rup_sound cl_14705 [cl_14698,cl_14697,cl_14545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14545 v h) (by intro d hd; cases hd))))
def cl_14706 : CNF.NClause := [(1054,false)]
theorem der_14706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14706 :=
  CNF.rup_sound cl_14706 [cl_14698,cl_14696,cl_14666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14666 v h) (by intro d hd; cases hd))))
def cl_14707 : CNF.NClause := [(1079,false)]
theorem der_14707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14707 :=
  CNF.rup_sound cl_14707 [cl_14698,cl_14697,cl_14691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14691 v h) (by intro d hd; cases hd))))
def cl_14710 : CNF.NClause := [(95,true),(56,true),(43,false),(33,false),(48,false),(53,false)]
theorem der_14710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14710 :=
  CNF.rup_sound cl_14710 [cl_2145,cl_2147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2145 v h) (hints_cons _ _ _ (inp_2147 v h) (by intro d hd; cases hd)))
def cl_14712 : CNF.NClause := [(64,true),(17,false),(2,false),(22,false),(12,false)]
theorem der_14712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14712 :=
  CNF.rup_sound cl_14712 [cl_14697,cl_161,cl_163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_161 v h) (hints_cons _ _ _ (inp_163 v h) (by intro d hd; cases hd))))
def cl_14714 : CNF.NClause := [(71,true),(13,false),(20,false),(19,false),(26,false),(1,false)]
theorem der_14714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14714 :=
  CNF.rup_sound cl_14714 [cl_577,cl_579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_577 v h) (hints_cons _ _ _ (inp_579 v h) (by intro d hd; cases hd)))
def cl_14716 : CNF.NClause := [(73,true),(18,false),(4,false),(28,false),(10,false),(21,false)]
theorem der_14716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14716 :=
  CNF.rup_sound cl_14716 [cl_705,cl_707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_705 v h) (hints_cons _ _ _ (inp_707 v h) (by intro d hd; cases hd)))
def cl_14718 : CNF.NClause := [(80,true),(24,false),(3,false),(29,false),(11,false),(15,false)]
theorem der_14718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14718 :=
  CNF.rup_sound cl_14718 [cl_1153,cl_1155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1153 v h) (hints_cons _ _ _ (inp_1155 v h) (by intro d hd; cases hd)))
def cl_14720 : CNF.NClause := [(82,true),(9,true),(5,false),(6,false),(8,false)]
theorem der_14720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14720 :=
  CNF.rup_sound cl_14720 [cl_14698,cl_1329,cl_1333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1329 v h) (hints_cons _ _ _ (inp_1333 v h) (by intro d hd; cases hd))))
def cl_14722 : CNF.NClause := [(89,true),(14,false),(23,false),(27,false),(16,false)]
theorem der_14722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14722 :=
  CNF.rup_sound cl_14722 [cl_14696,cl_1730,cl_1732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1730 v h) (hints_cons _ _ _ (inp_1732 v h) (by intro d hd; cases hd))))
def cl_14729 : CNF.NClause := [(82,true),(7,false),(8,false),(6,false),(5,false)]
theorem der_14729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14729 :=
  CNF.rup_sound cl_14729 [cl_14698,cl_1313,cl_14720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1313 v h) (hints_cons _ _ _ (der_14720 v h) (by intro d hd; cases hd))))
def cl_14736 : CNF.NClause := [(82,true),(7,true),(8,false),(5,false),(6,false)]
theorem der_14736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14736 :=
  CNF.rup_sound cl_14736 [cl_14698,cl_1317,cl_14720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1317 v h) (hints_cons _ _ _ (der_14720 v h) (by intro d hd; cases hd))))
def cl_15001 : CNF.NClause := [(62,true),(27,false),(26,false),(28,false),(29,false)]
theorem der_15001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15001 :=
  CNF.rup_sound cl_15001 [cl_14697,cl_14698,cl_34] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_34 v h) (by intro d hd; cases hd))))
def cl_15002 : CNF.NClause := [(62,true),(26,true),(27,false),(28,false),(29,false)]
theorem der_15002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15002 :=
  CNF.rup_sound cl_15002 [cl_14697,cl_14698,cl_36] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_36 v h) (by intro d hd; cases hd))))
def cl_15003 : CNF.NClause := [(62,true),(27,true),(26,false),(28,false),(29,false)]
theorem der_15003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15003 :=
  CNF.rup_sound cl_15003 [cl_14697,cl_14698,cl_38] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_38 v h) (by intro d hd; cases hd))))
def cl_15004 : CNF.NClause := [(62,true),(28,false),(27,true),(26,true),(29,false)]
theorem der_15004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15004 :=
  CNF.rup_sound cl_15004 [cl_14697,cl_14698,cl_40] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_40 v h) (by intro d hd; cases hd))))
def cl_15005 : CNF.NClause := [(62,true),(28,true),(26,false),(27,false),(29,false)]
theorem der_15005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15005 :=
  CNF.rup_sound cl_15005 [cl_14697,cl_14698,cl_42] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_42 v h) (by intro d hd; cases hd))))
def cl_15006 : CNF.NClause := [(62,true),(26,true),(27,false),(28,true),(29,false)]
theorem der_15006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15006 :=
  CNF.rup_sound cl_15006 [cl_14697,cl_14698,cl_44] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_44 v h) (by intro d hd; cases hd))))
def cl_15007 : CNF.NClause := [(62,true),(27,true),(26,false),(28,true),(29,false)]
theorem der_15007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15007 :=
  CNF.rup_sound cl_15007 [cl_14697,cl_14698,cl_46] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_46 v h) (by intro d hd; cases hd))))
def cl_15008 : CNF.NClause := [(28,true),(27,true),(29,false),(26,true),(62,false)]
theorem der_15008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15008 :=
  CNF.rup_sound cl_15008 [cl_14697,cl_14698,cl_48] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_48 v h) (by intro d hd; cases hd))))
def cl_15009 : CNF.NClause := [(62,true),(29,true),(26,false),(27,false),(28,false)]
theorem der_15009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15009 :=
  CNF.rup_sound cl_15009 [cl_14697,cl_14698,cl_50] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_50 v h) (by intro d hd; cases hd))))
def cl_15010 : CNF.NClause := [(62,true),(26,true),(27,false),(28,false),(29,true)]
theorem der_15010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15010 :=
  CNF.rup_sound cl_15010 [cl_14697,cl_14698,cl_52] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_52 v h) (by intro d hd; cases hd))))
def cl_15011 : CNF.NClause := [(62,true),(27,true),(26,false),(28,false),(29,true)]
theorem der_15011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15011 :=
  CNF.rup_sound cl_15011 [cl_14697,cl_14698,cl_54] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_54 v h) (by intro d hd; cases hd))))
def cl_15012 : CNF.NClause := [(28,false),(26,true),(27,true),(62,false),(29,true)]
theorem der_15012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15012 :=
  CNF.rup_sound cl_15012 [cl_14697,cl_14698,cl_56] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_56 v h) (by intro d hd; cases hd))))
def cl_15013 : CNF.NClause := [(62,true),(28,true),(26,false),(27,false),(29,true)]
theorem der_15013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15013 :=
  CNF.rup_sound cl_15013 [cl_14697,cl_14698,cl_58] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_58 v h) (by intro d hd; cases hd))))
def cl_15014 : CNF.NClause := [(26,true),(27,false),(62,false),(28,true),(29,true)]
theorem der_15014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15014 :=
  CNF.rup_sound cl_15014 [cl_14697,cl_14698,cl_60] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_60 v h) (by intro d hd; cases hd))))
def cl_15015 : CNF.NClause := [(27,true),(28,true),(62,false),(26,false),(29,true)]
theorem der_15015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15015 :=
  CNF.rup_sound cl_15015 [cl_14697,cl_14698,cl_62] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_62 v h) (by intro d hd; cases hd))))
def cl_15017 : CNF.NClause := [(63,true),(14,false),(4,false),(19,false),(9,false),(24,false)]
theorem der_15017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15017 :=
  CNF.rup_sound cl_15017 [cl_14697,cl_97] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_97 v h) (by intro d hd; cases hd)))
def cl_15018 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,false),(24,false)]
theorem der_15018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15018 :=
  CNF.rup_sound cl_15018 [cl_14697,cl_98] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_98 v h) (by intro d hd; cases hd)))
def cl_15019 : CNF.NClause := [(63,true),(14,false),(4,false),(9,true),(19,false),(24,false)]
theorem der_15019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15019 :=
  CNF.rup_sound cl_15019 [cl_14697,cl_99] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_99 v h) (by intro d hd; cases hd)))
def cl_15020 : CNF.NClause := [(63,true),(14,false),(9,true),(4,true),(19,false),(24,false)]
theorem der_15020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15020 :=
  CNF.rup_sound cl_15020 [cl_14697,cl_100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_100 v h) (by intro d hd; cases hd)))
def cl_15021 : CNF.NClause := [(63,true),(14,true),(4,false),(9,false),(19,false),(24,false)]
theorem der_15021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15021 :=
  CNF.rup_sound cl_15021 [cl_14697,cl_101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_101 v h) (by intro d hd; cases hd)))
def cl_15022 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,false),(24,false)]
theorem der_15022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15022 :=
  CNF.rup_sound cl_15022 [cl_14697,cl_102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_102 v h) (by intro d hd; cases hd)))
def cl_15023 : CNF.NClause := [(63,true),(14,true),(4,false),(9,true),(19,false),(24,false)]
theorem der_15023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15023 :=
  CNF.rup_sound cl_15023 [cl_14697,cl_103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_103 v h) (by intro d hd; cases hd)))
def cl_15024 : CNF.NClause := [(63,true),(14,true),(9,true),(4,true),(19,false),(24,false)]
theorem der_15024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15024 :=
  CNF.rup_sound cl_15024 [cl_14697,cl_104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_104 v h) (by intro d hd; cases hd)))
def cl_15025 : CNF.NClause := [(63,true),(14,false),(4,false),(9,false),(19,true),(24,false)]
theorem der_15025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15025 :=
  CNF.rup_sound cl_15025 [cl_14697,cl_105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_105 v h) (by intro d hd; cases hd)))
def cl_15026 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,false)]
theorem der_15026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15026 :=
  CNF.rup_sound cl_15026 [cl_14697,cl_106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_106 v h) (by intro d hd; cases hd)))
def cl_15027 : CNF.NClause := [(63,true),(14,false),(4,false),(9,true),(19,true),(24,false)]
theorem der_15027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15027 :=
  CNF.rup_sound cl_15027 [cl_14697,cl_107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_107 v h) (by intro d hd; cases hd)))
def cl_15028 : CNF.NClause := [(63,true),(14,false),(9,true),(4,true),(19,true),(24,false)]
theorem der_15028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15028 :=
  CNF.rup_sound cl_15028 [cl_14697,cl_108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_108 v h) (by intro d hd; cases hd)))
def cl_15029 : CNF.NClause := [(63,true),(14,true),(4,false),(9,false),(19,true),(24,false)]
theorem der_15029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15029 :=
  CNF.rup_sound cl_15029 [cl_14697,cl_109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_109 v h) (by intro d hd; cases hd)))
def cl_15030 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,true),(24,false)]
theorem der_15030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15030 :=
  CNF.rup_sound cl_15030 [cl_14697,cl_110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_110 v h) (by intro d hd; cases hd)))
def cl_15031 : CNF.NClause := [(63,true),(14,true),(4,false),(9,true),(19,true),(24,false)]
theorem der_15031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15031 :=
  CNF.rup_sound cl_15031 [cl_14697,cl_111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_111 v h) (by intro d hd; cases hd)))
def cl_15032 : CNF.NClause := [(14,true),(9,true),(24,false),(4,true),(19,true),(63,false)]
theorem der_15032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15032 :=
  CNF.rup_sound cl_15032 [cl_14697,cl_112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_112 v h) (by intro d hd; cases hd)))
def cl_15033 : CNF.NClause := [(63,true),(24,true),(4,false),(9,false),(14,false),(19,false)]
theorem der_15033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15033 :=
  CNF.rup_sound cl_15033 [cl_14697,cl_113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_113 v h) (by intro d hd; cases hd)))
def cl_15034 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,false),(24,true)]
theorem der_15034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15034 :=
  CNF.rup_sound cl_15034 [cl_14697,cl_114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_114 v h) (by intro d hd; cases hd)))
def cl_15035 : CNF.NClause := [(63,true),(14,false),(4,false),(9,true),(19,false),(24,true)]
theorem der_15035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15035 :=
  CNF.rup_sound cl_15035 [cl_14697,cl_115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_115 v h) (by intro d hd; cases hd)))
def cl_15036 : CNF.NClause := [(63,true),(14,false),(9,true),(4,true),(19,false),(24,true)]
theorem der_15036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15036 :=
  CNF.rup_sound cl_15036 [cl_14697,cl_116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_116 v h) (by intro d hd; cases hd)))
def cl_15037 : CNF.NClause := [(63,true),(14,true),(4,false),(9,false),(19,false),(24,true)]
theorem der_15037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15037 :=
  CNF.rup_sound cl_15037 [cl_14697,cl_117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_117 v h) (by intro d hd; cases hd)))
def cl_15038 : CNF.NClause := [(63,true),(4,true),(9,false),(14,true),(19,false),(24,true)]
theorem der_15038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15038 :=
  CNF.rup_sound cl_15038 [cl_14697,cl_118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_118 v h) (by intro d hd; cases hd)))
def cl_15039 : CNF.NClause := [(63,true),(14,true),(4,false),(9,true),(19,false),(24,true)]
theorem der_15039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15039 :=
  CNF.rup_sound cl_15039 [cl_14697,cl_119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_119 v h) (by intro d hd; cases hd)))
def cl_15040 : CNF.NClause := [(14,true),(63,false),(9,true),(4,true),(19,false),(24,true)]
theorem der_15040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15040 :=
  CNF.rup_sound cl_15040 [cl_14697,cl_120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_120 v h) (by intro d hd; cases hd)))
def cl_15041 : CNF.NClause := [(63,true),(14,false),(4,false),(9,false),(19,true),(24,true)]
theorem der_15041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15041 :=
  CNF.rup_sound cl_15041 [cl_14697,cl_121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_121 v h) (by intro d hd; cases hd)))
def cl_15042 : CNF.NClause := [(63,true),(4,true),(9,false),(14,false),(19,true),(24,true)]
theorem der_15042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15042 :=
  CNF.rup_sound cl_15042 [cl_14697,cl_122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_122 v h) (by intro d hd; cases hd)))
def cl_15043 : CNF.NClause := [(63,true),(14,false),(4,false),(9,true),(19,true),(24,true)]
theorem der_15043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15043 :=
  CNF.rup_sound cl_15043 [cl_14697,cl_123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_123 v h) (by intro d hd; cases hd)))
def cl_15044 : CNF.NClause := [(4,true),(19,true),(9,true),(63,false),(14,false),(24,true)]
theorem der_15044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15044 :=
  CNF.rup_sound cl_15044 [cl_14697,cl_124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_124 v h) (by intro d hd; cases hd)))
def cl_15045 : CNF.NClause := [(63,true),(14,true),(4,false),(9,false),(19,true),(24,true)]
theorem der_15045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15045 :=
  CNF.rup_sound cl_15045 [cl_14697,cl_125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_125 v h) (by intro d hd; cases hd)))
def cl_15046 : CNF.NClause := [(4,true),(9,false),(63,false),(14,true),(19,true),(24,true)]
theorem der_15046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15046 :=
  CNF.rup_sound cl_15046 [cl_14697,cl_126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_126 v h) (by intro d hd; cases hd)))
def cl_15047 : CNF.NClause := [(9,true),(14,true),(63,false),(4,false),(19,true),(24,true)]
theorem der_15047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15047 :=
  CNF.rup_sound cl_15047 [cl_14697,cl_127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_127 v h) (by intro d hd; cases hd)))
def cl_15048 : CNF.NClause := [(24,true),(14,true),(9,true),(4,true),(19,true),(63,false)]
theorem der_15048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15048 :=
  CNF.rup_sound cl_15048 [cl_14697,cl_128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_128 v h) (by intro d hd; cases hd)))
def cl_15049 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,false)]
theorem der_15049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15049 :=
  CNF.rup_sound cl_15049 [cl_14697,cl_162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_162 v h) (by intro d hd; cases hd)))
def cl_15050 : CNF.NClause := [(64,true),(17,false),(2,true),(12,false),(7,true),(22,false)]
theorem der_15050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15050 :=
  CNF.rup_sound cl_15050 [cl_14697,cl_164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_164 v h) (by intro d hd; cases hd)))
def cl_15051 : CNF.NClause := [(64,true),(12,true),(2,false),(7,false),(17,false),(22,false)]
theorem der_15051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15051 :=
  CNF.rup_sound cl_15051 [cl_14697,cl_165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_165 v h) (by intro d hd; cases hd)))
def cl_15052 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,false)]
theorem der_15052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15052 :=
  CNF.rup_sound cl_15052 [cl_14697,cl_166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_166 v h) (by intro d hd; cases hd)))
def cl_15053 : CNF.NClause := [(64,true),(7,true),(2,false),(12,true),(17,false),(22,false)]
theorem der_15053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15053 :=
  CNF.rup_sound cl_15053 [cl_14697,cl_167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_167 v h) (by intro d hd; cases hd)))
def cl_15054 : CNF.NClause := [(64,true),(17,false),(2,true),(7,true),(12,true),(22,false)]
theorem der_15054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15054 :=
  CNF.rup_sound cl_15054 [cl_14697,cl_168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_168 v h) (by intro d hd; cases hd)))
def cl_15055 : CNF.NClause := [(64,true),(17,true),(2,false),(7,false),(12,false),(22,false)]
theorem der_15055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15055 :=
  CNF.rup_sound cl_15055 [cl_14697,cl_169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_169 v h) (by intro d hd; cases hd)))
def cl_15056 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,false)]
theorem der_15056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15056 :=
  CNF.rup_sound cl_15056 [cl_14697,cl_170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_170 v h) (by intro d hd; cases hd)))
def cl_15057 : CNF.NClause := [(64,true),(17,true),(2,false),(12,false),(7,true),(22,false)]
theorem der_15057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15057 :=
  CNF.rup_sound cl_15057 [cl_14697,cl_171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_171 v h) (by intro d hd; cases hd)))
def cl_15058 : CNF.NClause := [(64,true),(17,true),(2,true),(12,false),(7,true),(22,false)]
theorem der_15058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15058 :=
  CNF.rup_sound cl_15058 [cl_14697,cl_172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_172 v h) (by intro d hd; cases hd)))
def cl_15059 : CNF.NClause := [(64,true),(12,true),(2,false),(7,false),(17,true),(22,false)]
theorem der_15059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15059 :=
  CNF.rup_sound cl_15059 [cl_14697,cl_173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_173 v h) (by intro d hd; cases hd)))
def cl_15060 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,true),(22,false)]
theorem der_15060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15060 :=
  CNF.rup_sound cl_15060 [cl_14697,cl_174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_174 v h) (by intro d hd; cases hd)))
def cl_15061 : CNF.NClause := [(64,true),(7,true),(2,false),(12,true),(17,true),(22,false)]
theorem der_15061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15061 :=
  CNF.rup_sound cl_15061 [cl_14697,cl_175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_175 v h) (by intro d hd; cases hd)))
def cl_15062 : CNF.NClause := [(17,true),(12,true),(2,true),(7,true),(64,false),(22,false)]
theorem der_15062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15062 :=
  CNF.rup_sound cl_15062 [cl_14697,cl_176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_176 v h) (by intro d hd; cases hd)))
def cl_15063 : CNF.NClause := [(64,true),(17,false),(2,false),(7,false),(12,false),(22,true)]
theorem der_15063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15063 :=
  CNF.rup_sound cl_15063 [cl_14697,cl_177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_177 v h) (by intro d hd; cases hd)))
def cl_15064 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,false),(22,true)]
theorem der_15064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15064 :=
  CNF.rup_sound cl_15064 [cl_14697,cl_178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_178 v h) (by intro d hd; cases hd)))
def cl_15065 : CNF.NClause := [(64,true),(17,false),(2,false),(12,false),(7,true),(22,true)]
theorem der_15065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15065 :=
  CNF.rup_sound cl_15065 [cl_14697,cl_179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_179 v h) (by intro d hd; cases hd)))
def cl_15066 : CNF.NClause := [(64,true),(17,false),(2,true),(12,false),(7,true),(22,true)]
theorem der_15066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15066 :=
  CNF.rup_sound cl_15066 [cl_14697,cl_180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_180 v h) (by intro d hd; cases hd)))
def cl_15067 : CNF.NClause := [(64,true),(12,true),(2,false),(7,false),(17,false),(22,true)]
theorem der_15067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15067 :=
  CNF.rup_sound cl_15067 [cl_14697,cl_181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_181 v h) (by intro d hd; cases hd)))
def cl_15068 : CNF.NClause := [(64,true),(2,true),(7,false),(12,true),(17,false),(22,true)]
theorem der_15068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15068 :=
  CNF.rup_sound cl_15068 [cl_14697,cl_182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_182 v h) (by intro d hd; cases hd)))
def cl_15069 : CNF.NClause := [(64,true),(7,true),(2,false),(12,true),(17,false),(22,true)]
theorem der_15069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15069 :=
  CNF.rup_sound cl_15069 [cl_14697,cl_183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_183 v h) (by intro d hd; cases hd)))
def cl_15070 : CNF.NClause := [(22,true),(2,true),(17,false),(7,true),(12,true),(64,false)]
theorem der_15070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15070 :=
  CNF.rup_sound cl_15070 [cl_14697,cl_184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_184 v h) (by intro d hd; cases hd)))
def cl_15071 : CNF.NClause := [(64,true),(17,true),(2,false),(7,false),(12,false),(22,true)]
theorem der_15071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15071 :=
  CNF.rup_sound cl_15071 [cl_14697,cl_185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_185 v h) (by intro d hd; cases hd)))
def cl_15072 : CNF.NClause := [(64,true),(2,true),(7,false),(12,false),(17,true),(22,true)]
theorem der_15072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15072 :=
  CNF.rup_sound cl_15072 [cl_14697,cl_186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_186 v h) (by intro d hd; cases hd)))
def cl_15073 : CNF.NClause := [(64,true),(17,true),(2,false),(12,false),(7,true),(22,true)]
theorem der_15073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15073 :=
  CNF.rup_sound cl_15073 [cl_14697,cl_187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_187 v h) (by intro d hd; cases hd)))
def cl_15074 : CNF.NClause := [(7,true),(64,false),(2,true),(12,false),(17,true),(22,true)]
theorem der_15074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15074 :=
  CNF.rup_sound cl_15074 [cl_14697,cl_188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_188 v h) (by intro d hd; cases hd)))
def cl_15075 : CNF.NClause := [(64,true),(12,true),(2,false),(7,false),(17,true),(22,true)]
theorem der_15075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15075 :=
  CNF.rup_sound cl_15075 [cl_14697,cl_189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_189 v h) (by intro d hd; cases hd)))
def cl_15076 : CNF.NClause := [(2,true),(12,true),(64,false),(7,false),(17,true),(22,true)]
theorem der_15076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15076 :=
  CNF.rup_sound cl_15076 [cl_14697,cl_190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_190 v h) (by intro d hd; cases hd)))
def cl_15077 : CNF.NClause := [(7,true),(64,false),(2,false),(12,true),(17,true),(22,true)]
theorem der_15077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15077 :=
  CNF.rup_sound cl_15077 [cl_14697,cl_191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_191 v h) (by intro d hd; cases hd)))
def cl_15078 : CNF.NClause := [(17,true),(12,true),(2,true),(7,true),(64,false),(22,true)]
theorem der_15078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15078 :=
  CNF.rup_sound cl_15078 [cl_14697,cl_192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_192 v h) (by intro d hd; cases hd)))
def cl_15079 : CNF.NClause := [(65,true),(13,false),(3,false),(8,false),(18,false),(23,false)]
theorem der_15079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15079 :=
  CNF.rup_sound cl_15079 [cl_14697,cl_225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_225 v h) (by intro d hd; cases hd)))
def cl_15080 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,false)]
theorem der_15080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15080 :=
  CNF.rup_sound cl_15080 [cl_14697,cl_226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_226 v h) (by intro d hd; cases hd)))
def cl_15081 : CNF.NClause := [(65,true),(23,false),(8,true),(13,false),(18,false),(3,false)]
theorem der_15081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15081 :=
  CNF.rup_sound cl_15081 [cl_14697,cl_227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_227 v h) (by intro d hd; cases hd)))
def cl_15082 : CNF.NClause := [(65,true),(13,false),(3,true),(8,true),(18,false),(23,false)]
theorem der_15082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15082 :=
  CNF.rup_sound cl_15082 [cl_14697,cl_228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_228 v h) (by intro d hd; cases hd)))
def cl_15083 : CNF.NClause := [(65,true),(13,true),(3,false),(8,false),(18,false),(23,false)]
theorem der_15083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15083 :=
  CNF.rup_sound cl_15083 [cl_14697,cl_229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_229 v h) (by intro d hd; cases hd)))
def cl_15084 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,false)]
theorem der_15084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15084 :=
  CNF.rup_sound cl_15084 [cl_14697,cl_230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_230 v h) (by intro d hd; cases hd)))
def cl_15085 : CNF.NClause := [(65,true),(13,true),(8,true),(3,false),(18,false),(23,false)]
theorem der_15085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15085 :=
  CNF.rup_sound cl_15085 [cl_14697,cl_231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_231 v h) (by intro d hd; cases hd)))
def cl_15086 : CNF.NClause := [(65,true),(13,true),(3,true),(8,true),(18,false),(23,false)]
theorem der_15086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15086 :=
  CNF.rup_sound cl_15086 [cl_14697,cl_232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_232 v h) (by intro d hd; cases hd)))
def cl_15087 : CNF.NClause := [(65,true),(13,false),(3,false),(8,false),(18,true),(23,false)]
theorem der_15087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15087 :=
  CNF.rup_sound cl_15087 [cl_14697,cl_233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_233 v h) (by intro d hd; cases hd)))
def cl_15088 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,true),(23,false)]
theorem der_15088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15088 :=
  CNF.rup_sound cl_15088 [cl_14697,cl_234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_234 v h) (by intro d hd; cases hd)))
def cl_15089 : CNF.NClause := [(65,true),(18,true),(8,true),(13,false),(3,false),(23,false)]
theorem der_15089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15089 :=
  CNF.rup_sound cl_15089 [cl_14697,cl_235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_235 v h) (by intro d hd; cases hd)))
def cl_15090 : CNF.NClause := [(65,true),(13,false),(3,true),(8,true),(18,true),(23,false)]
theorem der_15090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15090 :=
  CNF.rup_sound cl_15090 [cl_14697,cl_236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_236 v h) (by intro d hd; cases hd)))
def cl_15091 : CNF.NClause := [(65,true),(13,true),(3,false),(8,false),(18,true),(23,false)]
theorem der_15091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15091 :=
  CNF.rup_sound cl_15091 [cl_14697,cl_237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_237 v h) (by intro d hd; cases hd)))
def cl_15092 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,true),(23,false)]
theorem der_15092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15092 :=
  CNF.rup_sound cl_15092 [cl_14697,cl_238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_238 v h) (by intro d hd; cases hd)))
def cl_15093 : CNF.NClause := [(65,true),(13,true),(8,true),(3,false),(18,true),(23,false)]
theorem der_15093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15093 :=
  CNF.rup_sound cl_15093 [cl_14697,cl_239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_239 v h) (by intro d hd; cases hd)))
def cl_15094 : CNF.NClause := [(13,true),(65,false),(3,true),(8,true),(18,true),(23,false)]
theorem der_15094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15094 :=
  CNF.rup_sound cl_15094 [cl_14697,cl_240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_240 v h) (by intro d hd; cases hd)))
def cl_15095 : CNF.NClause := [(65,true),(13,false),(3,false),(8,false),(18,false),(23,true)]
theorem der_15095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15095 :=
  CNF.rup_sound cl_15095 [cl_14697,cl_241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_241 v h) (by intro d hd; cases hd)))
def cl_15096 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,false),(23,true)]
theorem der_15096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15096 :=
  CNF.rup_sound cl_15096 [cl_14697,cl_242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_242 v h) (by intro d hd; cases hd)))
def cl_15097 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,false),(23,true)]
theorem der_15097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15097 :=
  CNF.rup_sound cl_15097 [cl_14697,cl_243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_243 v h) (by intro d hd; cases hd)))
def cl_15098 : CNF.NClause := [(65,true),(13,false),(3,true),(8,true),(18,false),(23,true)]
theorem der_15098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15098 :=
  CNF.rup_sound cl_15098 [cl_14697,cl_244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_244 v h) (by intro d hd; cases hd)))
def cl_15099 : CNF.NClause := [(65,true),(13,true),(3,false),(8,false),(18,false),(23,true)]
theorem der_15099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15099 :=
  CNF.rup_sound cl_15099 [cl_14697,cl_245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_245 v h) (by intro d hd; cases hd)))
def cl_15100 : CNF.NClause := [(65,true),(3,true),(8,false),(13,true),(18,false),(23,true)]
theorem der_15100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15100 :=
  CNF.rup_sound cl_15100 [cl_14697,cl_246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_246 v h) (by intro d hd; cases hd)))
def cl_15101 : CNF.NClause := [(65,true),(3,false),(8,true),(13,true),(18,false),(23,true)]
theorem der_15101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15101 :=
  CNF.rup_sound cl_15101 [cl_14697,cl_247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_247 v h) (by intro d hd; cases hd)))
def cl_15102 : CNF.NClause := [(3,true),(8,true),(65,false),(18,false),(13,true),(23,true)]
theorem der_15102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15102 :=
  CNF.rup_sound cl_15102 [cl_14697,cl_248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_248 v h) (by intro d hd; cases hd)))
def cl_15103 : CNF.NClause := [(65,true),(13,false),(3,false),(8,false),(18,true),(23,true)]
theorem der_15103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15103 :=
  CNF.rup_sound cl_15103 [cl_14697,cl_249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_249 v h) (by intro d hd; cases hd)))
def cl_15104 : CNF.NClause := [(65,true),(3,true),(8,false),(13,false),(18,true),(23,true)]
theorem der_15104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15104 :=
  CNF.rup_sound cl_15104 [cl_14697,cl_250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_250 v h) (by intro d hd; cases hd)))
def cl_15105 : CNF.NClause := [(65,true),(3,false),(8,true),(13,false),(18,true),(23,true)]
theorem der_15105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15105 :=
  CNF.rup_sound cl_15105 [cl_14697,cl_251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_251 v h) (by intro d hd; cases hd)))
def cl_15106 : CNF.NClause := [(13,false),(65,false),(3,true),(8,true),(18,true),(23,true)]
theorem der_15106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15106 :=
  CNF.rup_sound cl_15106 [cl_14697,cl_252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_252 v h) (by intro d hd; cases hd)))
def cl_15107 : CNF.NClause := [(65,true),(13,true),(3,false),(8,false),(18,true),(23,true)]
theorem der_15107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15107 :=
  CNF.rup_sound cl_15107 [cl_14697,cl_253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_253 v h) (by intro d hd; cases hd)))
def cl_15108 : CNF.NClause := [(3,true),(8,false),(65,false),(13,true),(18,true),(23,true)]
theorem der_15108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15108 :=
  CNF.rup_sound cl_15108 [cl_14697,cl_254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_254 v h) (by intro d hd; cases hd)))
def cl_15109 : CNF.NClause := [(13,true),(18,true),(8,true),(65,false),(3,false),(23,true)]
theorem der_15109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15109 :=
  CNF.rup_sound cl_15109 [cl_14697,cl_255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_255 v h) (by intro d hd; cases hd)))
def cl_15110 : CNF.NClause := [(13,true),(65,false),(3,true),(8,true),(18,true),(23,true)]
theorem der_15110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15110 :=
  CNF.rup_sound cl_15110 [cl_14697,cl_256] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_256 v h) (by intro d hd; cases hd)))
def cl_15111 : CNF.NClause := [(66,true),(16,false),(1,false),(6,false),(11,false),(21,false)]
theorem der_15111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15111 :=
  CNF.rup_sound cl_15111 [cl_14697,cl_289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_289 v h) (by intro d hd; cases hd)))
def cl_15112 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,false)]
theorem der_15112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15112 :=
  CNF.rup_sound cl_15112 [cl_14697,cl_290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_290 v h) (by intro d hd; cases hd)))
def cl_15113 : CNF.NClause := [(66,true),(6,true),(1,false),(11,false),(16,false),(21,false)]
theorem der_15113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15113 :=
  CNF.rup_sound cl_15113 [cl_14697,cl_291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_291 v h) (by intro d hd; cases hd)))
def cl_15114 : CNF.NClause := [(66,true),(6,true),(1,true),(11,false),(16,false),(21,false)]
theorem der_15114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15114 :=
  CNF.rup_sound cl_15114 [cl_14697,cl_292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_292 v h) (by intro d hd; cases hd)))
def cl_15115 : CNF.NClause := [(66,true),(11,true),(1,false),(6,false),(16,false),(21,false)]
theorem der_15115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15115 :=
  CNF.rup_sound cl_15115 [cl_14697,cl_293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_293 v h) (by intro d hd; cases hd)))
def cl_15116 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,false),(21,false)]
theorem der_15116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15116 :=
  CNF.rup_sound cl_15116 [cl_14697,cl_294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_294 v h) (by intro d hd; cases hd)))
def cl_15117 : CNF.NClause := [(66,true),(6,true),(1,false),(11,true),(16,false),(21,false)]
theorem der_15117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15117 :=
  CNF.rup_sound cl_15117 [cl_14697,cl_295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_295 v h) (by intro d hd; cases hd)))
def cl_15118 : CNF.NClause := [(66,true),(11,true),(1,true),(6,true),(16,false),(21,false)]
theorem der_15118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15118 :=
  CNF.rup_sound cl_15118 [cl_14697,cl_296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_296 v h) (by intro d hd; cases hd)))
def cl_15119 : CNF.NClause := [(66,true),(16,true),(1,false),(6,false),(11,false),(21,false)]
theorem der_15119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15119 :=
  CNF.rup_sound cl_15119 [cl_14697,cl_297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_297 v h) (by intro d hd; cases hd)))
def cl_15120 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,false)]
theorem der_15120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15120 :=
  CNF.rup_sound cl_15120 [cl_14697,cl_298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_298 v h) (by intro d hd; cases hd)))
def cl_15121 : CNF.NClause := [(66,true),(6,true),(1,false),(11,false),(16,true),(21,false)]
theorem der_15121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15121 :=
  CNF.rup_sound cl_15121 [cl_14697,cl_299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_299 v h) (by intro d hd; cases hd)))
def cl_15122 : CNF.NClause := [(66,true),(6,true),(1,true),(11,false),(16,true),(21,false)]
theorem der_15122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15122 :=
  CNF.rup_sound cl_15122 [cl_14697,cl_300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_300 v h) (by intro d hd; cases hd)))
def cl_15123 : CNF.NClause := [(66,true),(11,true),(1,false),(6,false),(16,true),(21,false)]
theorem der_15123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15123 :=
  CNF.rup_sound cl_15123 [cl_14697,cl_301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_301 v h) (by intro d hd; cases hd)))
def cl_15124 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,true),(21,false)]
theorem der_15124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15124 :=
  CNF.rup_sound cl_15124 [cl_14697,cl_302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_302 v h) (by intro d hd; cases hd)))
def cl_15125 : CNF.NClause := [(66,true),(6,true),(1,false),(11,true),(16,true),(21,false)]
theorem der_15125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15125 :=
  CNF.rup_sound cl_15125 [cl_14697,cl_303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_303 v h) (by intro d hd; cases hd)))
def cl_15126 : CNF.NClause := [(16,true),(1,true),(21,false),(6,true),(11,true),(66,false)]
theorem der_15126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15126 :=
  CNF.rup_sound cl_15126 [cl_14697,cl_304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_304 v h) (by intro d hd; cases hd)))
def cl_15127 : CNF.NClause := [(66,true),(16,false),(1,false),(6,false),(11,false),(21,true)]
theorem der_15127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15127 :=
  CNF.rup_sound cl_15127 [cl_14697,cl_305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_305 v h) (by intro d hd; cases hd)))
def cl_15128 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,false),(21,true)]
theorem der_15128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15128 :=
  CNF.rup_sound cl_15128 [cl_14697,cl_306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_306 v h) (by intro d hd; cases hd)))
def cl_15129 : CNF.NClause := [(66,true),(6,true),(1,false),(11,false),(16,false),(21,true)]
theorem der_15129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15129 :=
  CNF.rup_sound cl_15129 [cl_14697,cl_307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_307 v h) (by intro d hd; cases hd)))
def cl_15130 : CNF.NClause := [(66,true),(6,true),(1,true),(11,false),(16,false),(21,true)]
theorem der_15130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15130 :=
  CNF.rup_sound cl_15130 [cl_14697,cl_308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_308 v h) (by intro d hd; cases hd)))
def cl_15131 : CNF.NClause := [(66,true),(11,true),(1,false),(6,false),(16,false),(21,true)]
theorem der_15131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15131 :=
  CNF.rup_sound cl_15131 [cl_14697,cl_309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_309 v h) (by intro d hd; cases hd)))
def cl_15132 : CNF.NClause := [(66,true),(1,true),(6,false),(11,true),(16,false),(21,true)]
theorem der_15132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15132 :=
  CNF.rup_sound cl_15132 [cl_14697,cl_310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_310 v h) (by intro d hd; cases hd)))
def cl_15133 : CNF.NClause := [(66,true),(6,true),(1,false),(11,true),(16,false),(21,true)]
theorem der_15133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15133 :=
  CNF.rup_sound cl_15133 [cl_14697,cl_311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_311 v h) (by intro d hd; cases hd)))
def cl_15134 : CNF.NClause := [(11,true),(16,false),(1,true),(6,true),(66,false),(21,true)]
theorem der_15134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15134 :=
  CNF.rup_sound cl_15134 [cl_14697,cl_312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_312 v h) (by intro d hd; cases hd)))
def cl_15135 : CNF.NClause := [(66,true),(16,true),(1,false),(6,false),(11,false),(21,true)]
theorem der_15135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15135 :=
  CNF.rup_sound cl_15135 [cl_14697,cl_313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_313 v h) (by intro d hd; cases hd)))
def cl_15136 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(16,true),(21,true)]
theorem der_15136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15136 :=
  CNF.rup_sound cl_15136 [cl_14697,cl_314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_314 v h) (by intro d hd; cases hd)))
def cl_15137 : CNF.NClause := [(66,true),(6,true),(1,false),(11,false),(16,true),(21,true)]
theorem der_15137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15137 :=
  CNF.rup_sound cl_15137 [cl_14697,cl_315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_315 v h) (by intro d hd; cases hd)))
def cl_15138 : CNF.NClause := [(6,true),(11,false),(1,true),(66,false),(16,true),(21,true)]
theorem der_15138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15138 :=
  CNF.rup_sound cl_15138 [cl_14697,cl_316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_316 v h) (by intro d hd; cases hd)))
def cl_15139 : CNF.NClause := [(66,true),(11,true),(1,false),(6,false),(16,true),(21,true)]
theorem der_15139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15139 :=
  CNF.rup_sound cl_15139 [cl_14697,cl_317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_317 v h) (by intro d hd; cases hd)))
def cl_15140 : CNF.NClause := [(1,true),(11,true),(66,false),(6,false),(16,true),(21,true)]
theorem der_15140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15140 :=
  CNF.rup_sound cl_15140 [cl_14697,cl_318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_318 v h) (by intro d hd; cases hd)))
def cl_15141 : CNF.NClause := [(6,true),(1,false),(66,false),(11,true),(16,true),(21,true)]
theorem der_15141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15141 :=
  CNF.rup_sound cl_15141 [cl_14697,cl_319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_319 v h) (by intro d hd; cases hd)))
def cl_15142 : CNF.NClause := [(16,true),(66,false),(1,true),(6,true),(11,true),(21,true)]
theorem der_15142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15142 :=
  CNF.rup_sound cl_15142 [cl_14697,cl_320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_320 v h) (by intro d hd; cases hd)))
def cl_15143 : CNF.NClause := [(67,true),(21,false),(20,false),(23,false),(22,false),(24,false)]
theorem der_15143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15143 :=
  CNF.rup_sound cl_15143 [cl_14698,cl_353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_353 v h) (by intro d hd; cases hd)))
def cl_15144 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,false),(24,false)]
theorem der_15144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15144 :=
  CNF.rup_sound cl_15144 [cl_14698,cl_354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_354 v h) (by intro d hd; cases hd)))
def cl_15145 : CNF.NClause := [(67,true),(21,true),(20,false),(22,false),(23,false),(24,false)]
theorem der_15145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15145 :=
  CNF.rup_sound cl_15145 [cl_14698,cl_355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_355 v h) (by intro d hd; cases hd)))
def cl_15146 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,false)]
theorem der_15146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15146 :=
  CNF.rup_sound cl_15146 [cl_14698,cl_356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_356 v h) (by intro d hd; cases hd)))
def cl_15147 : CNF.NClause := [(67,true),(21,false),(20,false),(22,true),(23,false),(24,false)]
theorem der_15147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15147 :=
  CNF.rup_sound cl_15147 [cl_14698,cl_357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_357 v h) (by intro d hd; cases hd)))
def cl_15148 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,false),(24,false)]
theorem der_15148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15148 :=
  CNF.rup_sound cl_15148 [cl_14698,cl_358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_358 v h) (by intro d hd; cases hd)))
def cl_15149 : CNF.NClause := [(67,true),(21,true),(20,false),(22,true),(23,false),(24,false)]
theorem der_15149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15149 :=
  CNF.rup_sound cl_15149 [cl_14698,cl_359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_359 v h) (by intro d hd; cases hd)))
def cl_15150 : CNF.NClause := [(67,true),(20,true),(21,true),(22,true),(23,false),(24,false)]
theorem der_15150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15150 :=
  CNF.rup_sound cl_15150 [cl_14698,cl_360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_360 v h) (by intro d hd; cases hd)))
def cl_15151 : CNF.NClause := [(67,true),(23,true),(20,false),(21,false),(22,false),(24,false)]
theorem der_15151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15151 :=
  CNF.rup_sound cl_15151 [cl_14698,cl_361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_361 v h) (by intro d hd; cases hd)))
def cl_15152 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,true),(24,false)]
theorem der_15152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15152 :=
  CNF.rup_sound cl_15152 [cl_14698,cl_362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_362 v h) (by intro d hd; cases hd)))
def cl_15153 : CNF.NClause := [(67,true),(21,true),(20,false),(22,false),(23,true),(24,false)]
theorem der_15153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15153 :=
  CNF.rup_sound cl_15153 [cl_14698,cl_363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_363 v h) (by intro d hd; cases hd)))
def cl_15154 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,true),(24,false)]
theorem der_15154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15154 :=
  CNF.rup_sound cl_15154 [cl_14698,cl_364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_364 v h) (by intro d hd; cases hd)))
def cl_15155 : CNF.NClause := [(67,true),(21,false),(20,false),(22,true),(23,true),(24,false)]
theorem der_15155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15155 :=
  CNF.rup_sound cl_15155 [cl_14698,cl_365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_365 v h) (by intro d hd; cases hd)))
def cl_15156 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,true),(24,false)]
theorem der_15156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15156 :=
  CNF.rup_sound cl_15156 [cl_14698,cl_366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_366 v h) (by intro d hd; cases hd)))
def cl_15157 : CNF.NClause := [(67,true),(21,true),(20,false),(22,true),(23,true),(24,false)]
theorem der_15157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15157 :=
  CNF.rup_sound cl_15157 [cl_14698,cl_367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_367 v h) (by intro d hd; cases hd)))
def cl_15158 : CNF.NClause := [(67,false),(20,true),(21,true),(22,true),(23,true),(24,false)]
theorem der_15158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15158 :=
  CNF.rup_sound cl_15158 [cl_14698,cl_368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_368 v h) (by intro d hd; cases hd)))
def cl_15159 : CNF.NClause := [(67,true),(24,true),(20,false),(21,false),(22,false),(23,false)]
theorem der_15159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15159 :=
  CNF.rup_sound cl_15159 [cl_14698,cl_369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_369 v h) (by intro d hd; cases hd)))
def cl_15160 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,false),(24,true)]
theorem der_15160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15160 :=
  CNF.rup_sound cl_15160 [cl_14698,cl_370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_370 v h) (by intro d hd; cases hd)))
def cl_15161 : CNF.NClause := [(67,true),(21,true),(20,false),(22,false),(23,false),(24,true)]
theorem der_15161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15161 :=
  CNF.rup_sound cl_15161 [cl_14698,cl_371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_371 v h) (by intro d hd; cases hd)))
def cl_15162 : CNF.NClause := [(67,true),(20,true),(21,true),(22,false),(23,false),(24,true)]
theorem der_15162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15162 :=
  CNF.rup_sound cl_15162 [cl_14698,cl_372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_372 v h) (by intro d hd; cases hd)))
def cl_15163 : CNF.NClause := [(67,true),(21,false),(20,false),(22,true),(23,false),(24,true)]
theorem der_15163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15163 :=
  CNF.rup_sound cl_15163 [cl_14698,cl_373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_373 v h) (by intro d hd; cases hd)))
def cl_15164 : CNF.NClause := [(67,true),(20,true),(21,false),(22,true),(23,false),(24,true)]
theorem der_15164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15164 :=
  CNF.rup_sound cl_15164 [cl_14698,cl_374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_374 v h) (by intro d hd; cases hd)))
def cl_15165 : CNF.NClause := [(67,true),(21,true),(20,false),(22,true),(23,false),(24,true)]
theorem der_15165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15165 :=
  CNF.rup_sound cl_15165 [cl_14698,cl_375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_375 v h) (by intro d hd; cases hd)))
def cl_15166 : CNF.NClause := [(67,false),(20,true),(21,true),(22,true),(23,false),(24,true)]
theorem der_15166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15166 :=
  CNF.rup_sound cl_15166 [cl_14698,cl_376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_376 v h) (by intro d hd; cases hd)))
def cl_15167 : CNF.NClause := [(67,true),(23,true),(20,false),(21,false),(22,false),(24,true)]
theorem der_15167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15167 :=
  CNF.rup_sound cl_15167 [cl_14698,cl_377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_377 v h) (by intro d hd; cases hd)))
def cl_15168 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(23,true),(24,true)]
theorem der_15168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15168 :=
  CNF.rup_sound cl_15168 [cl_14698,cl_378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_378 v h) (by intro d hd; cases hd)))
def cl_15169 : CNF.NClause := [(67,true),(21,true),(20,false),(22,false),(23,true),(24,true)]
theorem der_15169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15169 :=
  CNF.rup_sound cl_15169 [cl_14698,cl_379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_379 v h) (by intro d hd; cases hd)))
def cl_15170 : CNF.NClause := [(67,false),(20,true),(21,true),(22,false),(23,true),(24,true)]
theorem der_15170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15170 :=
  CNF.rup_sound cl_15170 [cl_14698,cl_380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_380 v h) (by intro d hd; cases hd)))
def cl_15171 : CNF.NClause := [(67,true),(21,false),(20,false),(22,true),(23,true),(24,true)]
theorem der_15171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15171 :=
  CNF.rup_sound cl_15171 [cl_14698,cl_381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_381 v h) (by intro d hd; cases hd)))
def cl_15172 : CNF.NClause := [(67,false),(20,true),(21,false),(22,true),(23,true),(24,true)]
theorem der_15172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15172 :=
  CNF.rup_sound cl_15172 [cl_14698,cl_382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_382 v h) (by intro d hd; cases hd)))
def cl_15173 : CNF.NClause := [(67,false),(21,true),(20,false),(22,true),(23,true),(24,true)]
theorem der_15173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15173 :=
  CNF.rup_sound cl_15173 [cl_14698,cl_383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_383 v h) (by intro d hd; cases hd)))
def cl_15175 : CNF.NClause := [(72,true),(13,false),(10,false),(11,false),(12,false),(14,false)]
theorem der_15175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15175 :=
  CNF.rup_sound cl_15175 [cl_14698,cl_673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_673 v h) (by intro d hd; cases hd)))
def cl_15176 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,false)]
theorem der_15176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15176 :=
  CNF.rup_sound cl_15176 [cl_14698,cl_674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_674 v h) (by intro d hd; cases hd)))
def cl_15177 : CNF.NClause := [(72,true),(11,true),(10,false),(12,false),(13,false),(14,false)]
theorem der_15177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15177 :=
  CNF.rup_sound cl_15177 [cl_14698,cl_675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_675 v h) (by intro d hd; cases hd)))
def cl_15178 : CNF.NClause := [(72,true),(11,true),(10,true),(12,false),(13,false),(14,false)]
theorem der_15178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15178 :=
  CNF.rup_sound cl_15178 [cl_14698,cl_676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_676 v h) (by intro d hd; cases hd)))
def cl_15179 : CNF.NClause := [(72,true),(13,false),(10,false),(12,true),(11,false),(14,false)]
theorem der_15179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15179 :=
  CNF.rup_sound cl_15179 [cl_14698,cl_677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_677 v h) (by intro d hd; cases hd)))
def cl_15180 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,false)]
theorem der_15180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15180 :=
  CNF.rup_sound cl_15180 [cl_14698,cl_678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_678 v h) (by intro d hd; cases hd)))
def cl_15181 : CNF.NClause := [(72,true),(11,true),(10,false),(12,true),(13,false),(14,false)]
theorem der_15181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15181 :=
  CNF.rup_sound cl_15181 [cl_14698,cl_679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_679 v h) (by intro d hd; cases hd)))
def cl_15182 : CNF.NClause := [(72,true),(10,true),(13,false),(11,true),(12,true),(14,false)]
theorem der_15182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15182 :=
  CNF.rup_sound cl_15182 [cl_14698,cl_680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_680 v h) (by intro d hd; cases hd)))
def cl_15183 : CNF.NClause := [(72,true),(13,true),(10,false),(11,false),(12,false),(14,false)]
theorem der_15183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15183 :=
  CNF.rup_sound cl_15183 [cl_14698,cl_681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_681 v h) (by intro d hd; cases hd)))
def cl_15184 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,false)]
theorem der_15184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15184 :=
  CNF.rup_sound cl_15184 [cl_14698,cl_682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_682 v h) (by intro d hd; cases hd)))
def cl_15185 : CNF.NClause := [(72,true),(11,true),(10,false),(12,false),(13,true),(14,false)]
theorem der_15185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15185 :=
  CNF.rup_sound cl_15185 [cl_14698,cl_683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_683 v h) (by intro d hd; cases hd)))
def cl_15186 : CNF.NClause := [(72,true),(11,true),(10,true),(12,false),(13,true),(14,false)]
theorem der_15186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15186 :=
  CNF.rup_sound cl_15186 [cl_14698,cl_684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_684 v h) (by intro d hd; cases hd)))
def cl_15187 : CNF.NClause := [(72,true),(13,true),(10,false),(12,true),(11,false),(14,false)]
theorem der_15187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15187 :=
  CNF.rup_sound cl_15187 [cl_14698,cl_685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_685 v h) (by intro d hd; cases hd)))
def cl_15188 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,true),(14,false)]
theorem der_15188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15188 :=
  CNF.rup_sound cl_15188 [cl_14698,cl_686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_686 v h) (by intro d hd; cases hd)))
def cl_15189 : CNF.NClause := [(72,true),(11,true),(10,false),(12,true),(13,true),(14,false)]
theorem der_15189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15189 :=
  CNF.rup_sound cl_15189 [cl_14698,cl_687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_687 v h) (by intro d hd; cases hd)))
def cl_15190 : CNF.NClause := [(72,false),(13,true),(10,true),(11,true),(12,true),(14,false)]
theorem der_15190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15190 :=
  CNF.rup_sound cl_15190 [cl_14698,cl_688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_688 v h) (by intro d hd; cases hd)))
def cl_15191 : CNF.NClause := [(72,true),(13,false),(10,false),(11,false),(12,false),(14,true)]
theorem der_15191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15191 :=
  CNF.rup_sound cl_15191 [cl_14698,cl_689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_689 v h) (by intro d hd; cases hd)))
def cl_15192 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,false),(14,true)]
theorem der_15192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15192 :=
  CNF.rup_sound cl_15192 [cl_14698,cl_690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_690 v h) (by intro d hd; cases hd)))
def cl_15193 : CNF.NClause := [(72,true),(11,true),(10,false),(12,false),(13,false),(14,true)]
theorem der_15193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15193 :=
  CNF.rup_sound cl_15193 [cl_14698,cl_691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_691 v h) (by intro d hd; cases hd)))
def cl_15194 : CNF.NClause := [(72,true),(11,true),(10,true),(12,false),(13,false),(14,true)]
theorem der_15194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15194 :=
  CNF.rup_sound cl_15194 [cl_14698,cl_692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_692 v h) (by intro d hd; cases hd)))
def cl_15195 : CNF.NClause := [(72,true),(14,true),(10,false),(12,true),(13,false),(11,false)]
theorem der_15195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15195 :=
  CNF.rup_sound cl_15195 [cl_14698,cl_693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_693 v h) (by intro d hd; cases hd)))
def cl_15196 : CNF.NClause := [(72,true),(10,true),(11,false),(12,true),(13,false),(14,true)]
theorem der_15196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15196 :=
  CNF.rup_sound cl_15196 [cl_14698,cl_694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_694 v h) (by intro d hd; cases hd)))
def cl_15197 : CNF.NClause := [(72,true),(11,true),(10,false),(12,true),(13,false),(14,true)]
theorem der_15197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15197 :=
  CNF.rup_sound cl_15197 [cl_14698,cl_695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_695 v h) (by intro d hd; cases hd)))
def cl_15198 : CNF.NClause := [(72,false),(10,true),(13,false),(11,true),(12,true),(14,true)]
theorem der_15198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15198 :=
  CNF.rup_sound cl_15198 [cl_14698,cl_696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_696 v h) (by intro d hd; cases hd)))
def cl_15199 : CNF.NClause := [(72,true),(13,true),(10,false),(11,false),(12,false),(14,true)]
theorem der_15199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15199 :=
  CNF.rup_sound cl_15199 [cl_14698,cl_697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_697 v h) (by intro d hd; cases hd)))
def cl_15200 : CNF.NClause := [(72,true),(10,true),(11,false),(12,false),(13,true),(14,true)]
theorem der_15200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15200 :=
  CNF.rup_sound cl_15200 [cl_14698,cl_698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_698 v h) (by intro d hd; cases hd)))
def cl_15201 : CNF.NClause := [(72,true),(11,true),(10,false),(12,false),(13,true),(14,true)]
theorem der_15201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15201 :=
  CNF.rup_sound cl_15201 [cl_14698,cl_699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_699 v h) (by intro d hd; cases hd)))
def cl_15202 : CNF.NClause := [(72,false),(11,true),(10,true),(12,false),(13,true),(14,true)]
theorem der_15202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15202 :=
  CNF.rup_sound cl_15202 [cl_14698,cl_700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_700 v h) (by intro d hd; cases hd)))
def cl_15203 : CNF.NClause := [(72,true),(13,true),(10,false),(12,true),(11,false),(14,true)]
theorem der_15203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15203 :=
  CNF.rup_sound cl_15203 [cl_14698,cl_701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_701 v h) (by intro d hd; cases hd)))
def cl_15204 : CNF.NClause := [(10,true),(12,true),(11,false),(72,false),(13,true),(14,true)]
theorem der_15204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15204 :=
  CNF.rup_sound cl_15204 [cl_14698,cl_702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_702 v h) (by intro d hd; cases hd)))
def cl_15205 : CNF.NClause := [(72,false),(11,true),(10,false),(12,true),(13,true),(14,true)]
theorem der_15205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15205 :=
  CNF.rup_sound cl_15205 [cl_14698,cl_703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_703 v h) (by intro d hd; cases hd)))
def cl_15206 : CNF.NClause := [(72,false),(13,true),(10,true),(11,true),(12,true),(14,true)]
theorem der_15206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15206 :=
  CNF.rup_sound cl_15206 [cl_14698,cl_704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_704 v h) (by intro d hd; cases hd)))
def cl_15207 : CNF.NClause := [(77,true),(17,false),(15,false),(18,false),(16,false),(19,false)]
theorem der_15207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15207 :=
  CNF.rup_sound cl_15207 [cl_14698,cl_993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_993 v h) (by intro d hd; cases hd)))
def cl_15208 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,false),(19,false)]
theorem der_15208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15208 :=
  CNF.rup_sound cl_15208 [cl_14698,cl_994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_994 v h) (by intro d hd; cases hd)))
def cl_15209 : CNF.NClause := [(77,true),(17,false),(15,false),(16,true),(18,false),(19,false)]
theorem der_15209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15209 :=
  CNF.rup_sound cl_15209 [cl_14698,cl_995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_995 v h) (by intro d hd; cases hd)))
def cl_15210 : CNF.NClause := [(77,true),(15,true),(19,false),(16,true),(17,false),(18,false)]
theorem der_15210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15210 :=
  CNF.rup_sound cl_15210 [cl_14698,cl_996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_996 v h) (by intro d hd; cases hd)))
def cl_15211 : CNF.NClause := [(77,true),(17,true),(15,false),(16,false),(18,false),(19,false)]
theorem der_15211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15211 :=
  CNF.rup_sound cl_15211 [cl_14698,cl_997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_997 v h) (by intro d hd; cases hd)))
def cl_15212 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,false),(19,false)]
theorem der_15212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15212 :=
  CNF.rup_sound cl_15212 [cl_14698,cl_998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_998 v h) (by intro d hd; cases hd)))
def cl_15213 : CNF.NClause := [(77,true),(17,true),(15,false),(16,true),(18,false),(19,false)]
theorem der_15213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15213 :=
  CNF.rup_sound cl_15213 [cl_14698,cl_999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_999 v h) (by intro d hd; cases hd)))
def cl_15214 : CNF.NClause := [(77,true),(17,true),(15,true),(16,true),(18,false),(19,false)]
theorem der_15214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15214 :=
  CNF.rup_sound cl_15214 [cl_14698,cl_1000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1000 v h) (by intro d hd; cases hd)))
def cl_15215 : CNF.NClause := [(77,true),(17,false),(15,false),(16,false),(18,true),(19,false)]
theorem der_15215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15215 :=
  CNF.rup_sound cl_15215 [cl_14698,cl_1001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1001 v h) (by intro d hd; cases hd)))
def cl_15216 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,true),(19,false)]
theorem der_15216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15216 :=
  CNF.rup_sound cl_15216 [cl_14698,cl_1002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1002 v h) (by intro d hd; cases hd)))
def cl_15217 : CNF.NClause := [(77,true),(17,false),(15,false),(16,true),(18,true),(19,false)]
theorem der_15217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15217 :=
  CNF.rup_sound cl_15217 [cl_14698,cl_1003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1003 v h) (by intro d hd; cases hd)))
def cl_15218 : CNF.NClause := [(77,true),(17,false),(15,true),(16,true),(18,true),(19,false)]
theorem der_15218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15218 :=
  CNF.rup_sound cl_15218 [cl_14698,cl_1004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1004 v h) (by intro d hd; cases hd)))
def cl_15219 : CNF.NClause := [(77,true),(17,true),(15,false),(16,false),(18,true),(19,false)]
theorem der_15219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15219 :=
  CNF.rup_sound cl_15219 [cl_14698,cl_1005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1005 v h) (by intro d hd; cases hd)))
def cl_15220 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,true),(19,false)]
theorem der_15220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15220 :=
  CNF.rup_sound cl_15220 [cl_14698,cl_1006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1006 v h) (by intro d hd; cases hd)))
def cl_15221 : CNF.NClause := [(77,true),(17,true),(15,false),(16,true),(18,true),(19,false)]
theorem der_15221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15221 :=
  CNF.rup_sound cl_15221 [cl_14698,cl_1007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1007 v h) (by intro d hd; cases hd)))
def cl_15222 : CNF.NClause := [(77,false),(16,true),(15,true),(17,true),(18,true),(19,false)]
theorem der_15222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15222 :=
  CNF.rup_sound cl_15222 [cl_14698,cl_1008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1008 v h) (by intro d hd; cases hd)))
def cl_15223 : CNF.NClause := [(77,true),(17,false),(15,false),(16,false),(18,false),(19,true)]
theorem der_15223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15223 :=
  CNF.rup_sound cl_15223 [cl_14698,cl_1009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1009 v h) (by intro d hd; cases hd)))
def cl_15224 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,false),(19,true)]
theorem der_15224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15224 :=
  CNF.rup_sound cl_15224 [cl_14698,cl_1010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1010 v h) (by intro d hd; cases hd)))
def cl_15225 : CNF.NClause := [(77,true),(17,false),(15,false),(16,true),(18,false),(19,true)]
theorem der_15225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15225 :=
  CNF.rup_sound cl_15225 [cl_14698,cl_1011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1011 v h) (by intro d hd; cases hd)))
def cl_15226 : CNF.NClause := [(77,true),(15,true),(18,false),(16,true),(17,false),(19,true)]
theorem der_15226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15226 :=
  CNF.rup_sound cl_15226 [cl_14698,cl_1012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1012 v h) (by intro d hd; cases hd)))
def cl_15227 : CNF.NClause := [(77,true),(17,true),(15,false),(16,false),(18,false),(19,true)]
theorem der_15227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15227 :=
  CNF.rup_sound cl_15227 [cl_14698,cl_1013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1013 v h) (by intro d hd; cases hd)))
def cl_15228 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,false),(19,true)]
theorem der_15228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15228 :=
  CNF.rup_sound cl_15228 [cl_14698,cl_1014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1014 v h) (by intro d hd; cases hd)))
def cl_15229 : CNF.NClause := [(77,true),(17,true),(15,false),(16,true),(18,false),(19,true)]
theorem der_15229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15229 :=
  CNF.rup_sound cl_15229 [cl_14698,cl_1015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1015 v h) (by intro d hd; cases hd)))
def cl_15230 : CNF.NClause := [(77,false),(16,true),(15,true),(17,true),(18,false),(19,true)]
theorem der_15230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15230 :=
  CNF.rup_sound cl_15230 [cl_14698,cl_1016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1016 v h) (by intro d hd; cases hd)))
def cl_15231 : CNF.NClause := [(77,true),(17,false),(15,false),(16,false),(18,true),(19,true)]
theorem der_15231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15231 :=
  CNF.rup_sound cl_15231 [cl_14698,cl_1017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1017 v h) (by intro d hd; cases hd)))
def cl_15232 : CNF.NClause := [(77,true),(15,true),(16,false),(17,false),(18,true),(19,true)]
theorem der_15232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15232 :=
  CNF.rup_sound cl_15232 [cl_14698,cl_1018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1018 v h) (by intro d hd; cases hd)))
def cl_15233 : CNF.NClause := [(77,true),(17,false),(15,false),(16,true),(18,true),(19,true)]
theorem der_15233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15233 :=
  CNF.rup_sound cl_15233 [cl_14698,cl_1019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1019 v h) (by intro d hd; cases hd)))
def cl_15234 : CNF.NClause := [(77,false),(17,false),(15,true),(16,true),(18,true),(19,true)]
theorem der_15234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15234 :=
  CNF.rup_sound cl_15234 [cl_14698,cl_1020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1020 v h) (by intro d hd; cases hd)))
def cl_15235 : CNF.NClause := [(77,true),(17,true),(15,false),(16,false),(18,true),(19,true)]
theorem der_15235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15235 :=
  CNF.rup_sound cl_15235 [cl_14698,cl_1021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1021 v h) (by intro d hd; cases hd)))
def cl_15236 : CNF.NClause := [(77,false),(15,true),(16,false),(17,true),(18,true),(19,true)]
theorem der_15236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15236 :=
  CNF.rup_sound cl_15236 [cl_14698,cl_1022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1022 v h) (by intro d hd; cases hd)))
def cl_15237 : CNF.NClause := [(77,false),(17,true),(15,false),(16,true),(18,true),(19,true)]
theorem der_15237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15237 :=
  CNF.rup_sound cl_15237 [cl_14698,cl_1023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1023 v h) (by intro d hd; cases hd)))
def cl_15238 : CNF.NClause := [(77,false),(16,true),(15,true),(17,true),(18,true),(19,true)]
theorem der_15238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15238 :=
  CNF.rup_sound cl_15238 [cl_14698,cl_1024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1024 v h) (by intro d hd; cases hd)))
def cl_15239 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,false)]
theorem der_15239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15239 :=
  CNF.rup_sound cl_15239 [cl_14698,cl_1314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1314 v h) (by intro d hd; cases hd)))
def cl_15240 : CNF.NClause := [(82,true),(6,true),(5,false),(7,false),(8,false),(9,false)]
theorem der_15240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15240 :=
  CNF.rup_sound cl_15240 [cl_14698,cl_1315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1315 v h) (by intro d hd; cases hd)))
def cl_15241 : CNF.NClause := [(82,true),(6,true),(5,true),(7,false),(8,false),(9,false)]
theorem der_15241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15241 :=
  CNF.rup_sound cl_15241 [cl_14698,cl_1316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1316 v h) (by intro d hd; cases hd)))
def cl_15242 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,false)]
theorem der_15242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15242 :=
  CNF.rup_sound cl_15242 [cl_14698,cl_1318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1318 v h) (by intro d hd; cases hd)))
def cl_15243 : CNF.NClause := [(82,true),(6,true),(5,false),(7,true),(8,false),(9,false)]
theorem der_15243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15243 :=
  CNF.rup_sound cl_15243 [cl_14698,cl_1319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1319 v h) (by intro d hd; cases hd)))
def cl_15244 : CNF.NClause := [(82,true),(7,true),(5,true),(6,true),(8,false),(9,false)]
theorem der_15244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15244 :=
  CNF.rup_sound cl_15244 [cl_14698,cl_1320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1320 v h) (by intro d hd; cases hd)))
def cl_15245 : CNF.NClause := [(82,true),(8,true),(5,false),(6,false),(7,false),(9,false)]
theorem der_15245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15245 :=
  CNF.rup_sound cl_15245 [cl_14698,cl_1321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1321 v h) (by intro d hd; cases hd)))
def cl_15246 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,false)]
theorem der_15246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15246 :=
  CNF.rup_sound cl_15246 [cl_14698,cl_1322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1322 v h) (by intro d hd; cases hd)))
def cl_15247 : CNF.NClause := [(82,true),(6,true),(5,false),(7,false),(8,true),(9,false)]
theorem der_15247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15247 :=
  CNF.rup_sound cl_15247 [cl_14698,cl_1323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1323 v h) (by intro d hd; cases hd)))
def cl_15248 : CNF.NClause := [(82,true),(6,true),(5,true),(7,false),(8,true),(9,false)]
theorem der_15248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15248 :=
  CNF.rup_sound cl_15248 [cl_14698,cl_1324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1324 v h) (by intro d hd; cases hd)))
def cl_15249 : CNF.NClause := [(82,true),(7,true),(6,false),(5,false),(8,true),(9,false)]
theorem der_15249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15249 :=
  CNF.rup_sound cl_15249 [cl_14698,cl_1325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1325 v h) (by intro d hd; cases hd)))
def cl_15250 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,true),(9,false)]
theorem der_15250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15250 :=
  CNF.rup_sound cl_15250 [cl_14698,cl_1326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1326 v h) (by intro d hd; cases hd)))
def cl_15251 : CNF.NClause := [(82,true),(6,true),(5,false),(7,true),(8,true),(9,false)]
theorem der_15251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15251 :=
  CNF.rup_sound cl_15251 [cl_14698,cl_1327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1327 v h) (by intro d hd; cases hd)))
def cl_15252 : CNF.NClause := [(82,false),(8,true),(5,true),(6,true),(7,true),(9,false)]
theorem der_15252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15252 :=
  CNF.rup_sound cl_15252 [cl_14698,cl_1328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1328 v h) (by intro d hd; cases hd)))
def cl_15253 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,false),(9,true)]
theorem der_15253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15253 :=
  CNF.rup_sound cl_15253 [cl_14698,cl_1330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1330 v h) (by intro d hd; cases hd)))
def cl_15254 : CNF.NClause := [(82,true),(6,true),(5,false),(7,false),(8,false),(9,true)]
theorem der_15254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15254 :=
  CNF.rup_sound cl_15254 [cl_14698,cl_1331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1331 v h) (by intro d hd; cases hd)))
def cl_15255 : CNF.NClause := [(82,true),(6,true),(5,true),(7,false),(8,false),(9,true)]
theorem der_15255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15255 :=
  CNF.rup_sound cl_15255 [cl_14698,cl_1332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1332 v h) (by intro d hd; cases hd)))
def cl_15256 : CNF.NClause := [(82,true),(5,true),(6,false),(7,true),(8,false),(9,true)]
theorem der_15256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15256 :=
  CNF.rup_sound cl_15256 [cl_14698,cl_1334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1334 v h) (by intro d hd; cases hd)))
def cl_15257 : CNF.NClause := [(82,true),(6,true),(5,false),(7,true),(8,false),(9,true)]
theorem der_15257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15257 :=
  CNF.rup_sound cl_15257 [cl_14698,cl_1335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1335 v h) (by intro d hd; cases hd)))
def cl_15258 : CNF.NClause := [(82,false),(7,true),(5,true),(6,true),(8,false),(9,true)]
theorem der_15258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15258 :=
  CNF.rup_sound cl_15258 [cl_14698,cl_1336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1336 v h) (by intro d hd; cases hd)))
def cl_15259 : CNF.NClause := [(82,true),(8,true),(5,false),(6,false),(7,false),(9,true)]
theorem der_15259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15259 :=
  CNF.rup_sound cl_15259 [cl_14698,cl_1337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1337 v h) (by intro d hd; cases hd)))
def cl_15260 : CNF.NClause := [(82,true),(5,true),(6,false),(7,false),(8,true),(9,true)]
theorem der_15260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15260 :=
  CNF.rup_sound cl_15260 [cl_14698,cl_1338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1338 v h) (by intro d hd; cases hd)))
def cl_15261 : CNF.NClause := [(82,true),(6,true),(5,false),(7,false),(8,true),(9,true)]
theorem der_15261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15261 :=
  CNF.rup_sound cl_15261 [cl_14698,cl_1339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1339 v h) (by intro d hd; cases hd)))
def cl_15262 : CNF.NClause := [(82,false),(6,true),(5,true),(7,false),(8,true),(9,true)]
theorem der_15262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15262 :=
  CNF.rup_sound cl_15262 [cl_14698,cl_1340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1340 v h) (by intro d hd; cases hd)))
def cl_15263 : CNF.NClause := [(82,true),(7,true),(5,false),(6,false),(8,true),(9,true)]
theorem der_15263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15263 :=
  CNF.rup_sound cl_15263 [cl_14698,cl_1341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1341 v h) (by intro d hd; cases hd)))
def cl_15264 : CNF.NClause := [(82,false),(5,true),(6,false),(7,true),(8,true),(9,true)]
theorem der_15264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15264 :=
  CNF.rup_sound cl_15264 [cl_14698,cl_1342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1342 v h) (by intro d hd; cases hd)))
def cl_15265 : CNF.NClause := [(82,false),(6,true),(5,false),(7,true),(8,true),(9,true)]
theorem der_15265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15265 :=
  CNF.rup_sound cl_15265 [cl_14698,cl_1343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1343 v h) (by intro d hd; cases hd)))
def cl_15267 : CNF.NClause := [(87,true),(4,false),(3,false),(2,false),(1,false)]
theorem der_15267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15267 :=
  CNF.rup_sound cl_15267 [cl_14696,cl_14698,cl_1634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1634 v h) (by intro d hd; cases hd))))
def cl_15268 : CNF.NClause := [(87,true),(1,true),(2,false),(3,false),(4,false)]
theorem der_15268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15268 :=
  CNF.rup_sound cl_15268 [cl_14696,cl_14698,cl_1636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1636 v h) (by intro d hd; cases hd))))
def cl_15269 : CNF.NClause := [(87,true),(1,false),(2,true),(3,false),(4,false)]
theorem der_15269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15269 :=
  CNF.rup_sound cl_15269 [cl_14696,cl_14698,cl_1638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1638 v h) (by intro d hd; cases hd))))
def cl_15270 : CNF.NClause := [(87,true),(1,true),(3,false),(2,true),(4,false)]
theorem der_15270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15270 :=
  CNF.rup_sound cl_15270 [cl_14696,cl_14698,cl_1640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1640 v h) (by intro d hd; cases hd))))
def cl_15271 : CNF.NClause := [(87,true),(3,true),(1,false),(2,false),(4,false)]
theorem der_15271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15271 :=
  CNF.rup_sound cl_15271 [cl_14696,cl_14698,cl_1642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1642 v h) (by intro d hd; cases hd))))
def cl_15272 : CNF.NClause := [(87,true),(1,true),(2,false),(3,true),(4,false)]
theorem der_15272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15272 :=
  CNF.rup_sound cl_15272 [cl_14696,cl_14698,cl_1644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1644 v h) (by intro d hd; cases hd))))
def cl_15273 : CNF.NClause := [(87,true),(1,false),(2,true),(3,true),(4,false)]
theorem der_15273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15273 :=
  CNF.rup_sound cl_15273 [cl_14696,cl_14698,cl_1646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1646 v h) (by intro d hd; cases hd))))
def cl_15274 : CNF.NClause := [(87,false),(3,true),(1,true),(2,true),(4,false)]
theorem der_15274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15274 :=
  CNF.rup_sound cl_15274 [cl_14696,cl_14698,cl_1648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1648 v h) (by intro d hd; cases hd))))
def cl_15275 : CNF.NClause := [(87,true),(4,true),(1,false),(2,false),(3,false)]
theorem der_15275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15275 :=
  CNF.rup_sound cl_15275 [cl_14696,cl_14698,cl_1650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1650 v h) (by intro d hd; cases hd))))
def cl_15276 : CNF.NClause := [(87,true),(1,true),(2,false),(3,false),(4,true)]
theorem der_15276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15276 :=
  CNF.rup_sound cl_15276 [cl_14696,cl_14698,cl_1652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1652 v h) (by intro d hd; cases hd))))
def cl_15277 : CNF.NClause := [(87,true),(1,false),(2,true),(3,false),(4,true)]
theorem der_15277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15277 :=
  CNF.rup_sound cl_15277 [cl_14696,cl_14698,cl_1654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1654 v h) (by intro d hd; cases hd))))
def cl_15278 : CNF.NClause := [(87,false),(1,true),(3,false),(2,true),(4,true)]
theorem der_15278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15278 :=
  CNF.rup_sound cl_15278 [cl_14696,cl_14698,cl_1656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1656 v h) (by intro d hd; cases hd))))
def cl_15279 : CNF.NClause := [(87,true),(3,true),(1,false),(2,false),(4,true)]
theorem der_15279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15279 :=
  CNF.rup_sound cl_15279 [cl_14696,cl_14698,cl_1658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1658 v h) (by intro d hd; cases hd))))
def cl_15280 : CNF.NClause := [(87,false),(1,true),(2,false),(3,true),(4,true)]
theorem der_15280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15280 :=
  CNF.rup_sound cl_15280 [cl_14696,cl_14698,cl_1660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1660 v h) (by intro d hd; cases hd))))
def cl_15281 : CNF.NClause := [(87,false),(1,false),(2,true),(3,true),(4,true)]
theorem der_15281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15281 :=
  CNF.rup_sound cl_15281 [cl_14696,cl_14698,cl_1662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14698 v h) (hints_cons _ _ _ (inp_1662 v h) (by intro d hd; cases hd))))
def cl_15283 : CNF.NClause := [(88,true),(13,false),(21,false),(9,false),(17,false),(29,false)]
theorem der_15283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15283 :=
  CNF.rup_sound cl_15283 [cl_14696,cl_1666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1666 v h) (by intro d hd; cases hd)))
def cl_15284 : CNF.NClause := [(88,true),(13,false),(9,true),(17,false),(21,false),(29,false)]
theorem der_15284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15284 :=
  CNF.rup_sound cl_15284 [cl_14696,cl_1668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1668 v h) (by intro d hd; cases hd)))
def cl_15285 : CNF.NClause := [(88,true),(13,true),(9,false),(17,false),(21,false),(29,false)]
theorem der_15285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15285 :=
  CNF.rup_sound cl_15285 [cl_14696,cl_1670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1670 v h) (by intro d hd; cases hd)))
def cl_15286 : CNF.NClause := [(88,true),(13,true),(9,true),(17,false),(21,false),(29,false)]
theorem der_15286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15286 :=
  CNF.rup_sound cl_15286 [cl_14696,cl_1672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1672 v h) (by intro d hd; cases hd)))
def cl_15287 : CNF.NClause := [(88,true),(13,false),(9,false),(17,true),(21,false),(29,false)]
theorem der_15287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15287 :=
  CNF.rup_sound cl_15287 [cl_14696,cl_1674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1674 v h) (by intro d hd; cases hd)))
def cl_15288 : CNF.NClause := [(88,true),(13,false),(9,true),(17,true),(21,false),(29,false)]
theorem der_15288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15288 :=
  CNF.rup_sound cl_15288 [cl_14696,cl_1676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1676 v h) (by intro d hd; cases hd)))
def cl_15289 : CNF.NClause := [(88,true),(13,true),(9,false),(17,true),(21,false),(29,false)]
theorem der_15289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15289 :=
  CNF.rup_sound cl_15289 [cl_14696,cl_1678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1678 v h) (by intro d hd; cases hd)))
def cl_15290 : CNF.NClause := [(88,true),(13,true),(9,true),(17,true),(21,false),(29,false)]
theorem der_15290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15290 :=
  CNF.rup_sound cl_15290 [cl_14696,cl_1680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1680 v h) (by intro d hd; cases hd)))
def cl_15291 : CNF.NClause := [(88,true),(13,false),(17,false),(9,false),(21,true),(29,false)]
theorem der_15291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15291 :=
  CNF.rup_sound cl_15291 [cl_14696,cl_1682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1682 v h) (by intro d hd; cases hd)))
def cl_15292 : CNF.NClause := [(88,true),(13,false),(9,true),(17,false),(21,true),(29,false)]
theorem der_15292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15292 :=
  CNF.rup_sound cl_15292 [cl_14696,cl_1684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1684 v h) (by intro d hd; cases hd)))
def cl_15293 : CNF.NClause := [(88,true),(13,true),(9,false),(17,false),(21,true),(29,false)]
theorem der_15293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15293 :=
  CNF.rup_sound cl_15293 [cl_14696,cl_1686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1686 v h) (by intro d hd; cases hd)))
def cl_15294 : CNF.NClause := [(88,true),(13,true),(9,true),(17,false),(21,true),(29,false)]
theorem der_15294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15294 :=
  CNF.rup_sound cl_15294 [cl_14696,cl_1688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1688 v h) (by intro d hd; cases hd)))
def cl_15295 : CNF.NClause := [(88,true),(13,false),(9,false),(17,true),(21,true),(29,false)]
theorem der_15295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15295 :=
  CNF.rup_sound cl_15295 [cl_14696,cl_1690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1690 v h) (by intro d hd; cases hd)))
def cl_15296 : CNF.NClause := [(88,true),(13,false),(9,true),(17,true),(21,true),(29,false)]
theorem der_15296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15296 :=
  CNF.rup_sound cl_15296 [cl_14696,cl_1692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1692 v h) (by intro d hd; cases hd)))
def cl_15297 : CNF.NClause := [(88,true),(13,true),(9,false),(17,true),(21,true),(29,false)]
theorem der_15297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15297 :=
  CNF.rup_sound cl_15297 [cl_14696,cl_1694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1694 v h) (by intro d hd; cases hd)))
def cl_15298 : CNF.NClause := [(88,false),(13,true),(9,true),(17,true),(21,true),(29,false)]
theorem der_15298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15298 :=
  CNF.rup_sound cl_15298 [cl_14696,cl_1696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1696 v h) (by intro d hd; cases hd)))
def cl_15299 : CNF.NClause := [(88,true),(29,true),(9,false),(13,false),(17,false),(21,false)]
theorem der_15299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15299 :=
  CNF.rup_sound cl_15299 [cl_14696,cl_1698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1698 v h) (by intro d hd; cases hd)))
def cl_15300 : CNF.NClause := [(88,true),(13,false),(9,true),(17,false),(21,false),(29,true)]
theorem der_15300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15300 :=
  CNF.rup_sound cl_15300 [cl_14696,cl_1700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1700 v h) (by intro d hd; cases hd)))
def cl_15301 : CNF.NClause := [(88,true),(13,true),(9,false),(17,false),(21,false),(29,true)]
theorem der_15301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15301 :=
  CNF.rup_sound cl_15301 [cl_14696,cl_1702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1702 v h) (by intro d hd; cases hd)))
def cl_15302 : CNF.NClause := [(88,true),(13,true),(9,true),(17,false),(21,false),(29,true)]
theorem der_15302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15302 :=
  CNF.rup_sound cl_15302 [cl_14696,cl_1704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1704 v h) (by intro d hd; cases hd)))
def cl_15303 : CNF.NClause := [(88,true),(13,false),(9,false),(17,true),(21,false),(29,true)]
theorem der_15303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15303 :=
  CNF.rup_sound cl_15303 [cl_14696,cl_1706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1706 v h) (by intro d hd; cases hd)))
def cl_15304 : CNF.NClause := [(88,true),(13,false),(9,true),(17,true),(21,false),(29,true)]
theorem der_15304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15304 :=
  CNF.rup_sound cl_15304 [cl_14696,cl_1708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1708 v h) (by intro d hd; cases hd)))
def cl_15305 : CNF.NClause := [(88,true),(13,true),(9,false),(17,true),(21,false),(29,true)]
theorem der_15305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15305 :=
  CNF.rup_sound cl_15305 [cl_14696,cl_1710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1710 v h) (by intro d hd; cases hd)))
def cl_15306 : CNF.NClause := [(88,false),(9,true),(13,true),(17,true),(21,false),(29,true)]
theorem der_15306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15306 :=
  CNF.rup_sound cl_15306 [cl_14696,cl_1712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1712 v h) (by intro d hd; cases hd)))
def cl_15307 : CNF.NClause := [(88,true),(17,false),(9,false),(13,false),(21,true),(29,true)]
theorem der_15307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15307 :=
  CNF.rup_sound cl_15307 [cl_14696,cl_1714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1714 v h) (by intro d hd; cases hd)))
def cl_15308 : CNF.NClause := [(88,true),(13,false),(9,true),(17,false),(21,true),(29,true)]
theorem der_15308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15308 :=
  CNF.rup_sound cl_15308 [cl_14696,cl_1716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1716 v h) (by intro d hd; cases hd)))
def cl_15309 : CNF.NClause := [(88,true),(13,true),(9,false),(17,false),(21,true),(29,true)]
theorem der_15309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15309 :=
  CNF.rup_sound cl_15309 [cl_14696,cl_1718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1718 v h) (by intro d hd; cases hd)))
def cl_15310 : CNF.NClause := [(88,false),(9,true),(13,true),(17,false),(21,true),(29,true)]
theorem der_15310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15310 :=
  CNF.rup_sound cl_15310 [cl_14696,cl_1720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1720 v h) (by intro d hd; cases hd)))
def cl_15311 : CNF.NClause := [(88,true),(13,false),(9,false),(17,true),(21,true),(29,true)]
theorem der_15311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15311 :=
  CNF.rup_sound cl_15311 [cl_14696,cl_1722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1722 v h) (by intro d hd; cases hd)))
def cl_15312 : CNF.NClause := [(88,false),(13,false),(9,true),(17,true),(21,true),(29,true)]
theorem der_15312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15312 :=
  CNF.rup_sound cl_15312 [cl_14696,cl_1724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1724 v h) (by intro d hd; cases hd)))
def cl_15313 : CNF.NClause := [(88,false),(13,true),(9,false),(17,true),(21,true),(29,true)]
theorem der_15313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15313 :=
  CNF.rup_sound cl_15313 [cl_14696,cl_1726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1726 v h) (by intro d hd; cases hd)))
def cl_15315 : CNF.NClause := [(89,true),(14,true),(7,false),(16,false),(23,false),(27,false)]
theorem der_15315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15315 :=
  CNF.rup_sound cl_15315 [cl_14696,cl_1734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1734 v h) (by intro d hd; cases hd)))
def cl_15316 : CNF.NClause := [(89,true),(14,true),(16,false),(7,true),(23,false),(27,false)]
theorem der_15316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15316 :=
  CNF.rup_sound cl_15316 [cl_14696,cl_1736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1736 v h) (by intro d hd; cases hd)))
def cl_15317 : CNF.NClause := [(89,true),(14,false),(7,false),(16,true),(23,false),(27,false)]
theorem der_15317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15317 :=
  CNF.rup_sound cl_15317 [cl_14696,cl_1738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1738 v h) (by intro d hd; cases hd)))
def cl_15318 : CNF.NClause := [(89,true),(14,false),(16,true),(7,true),(23,false),(27,false)]
theorem der_15318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15318 :=
  CNF.rup_sound cl_15318 [cl_14696,cl_1740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1740 v h) (by intro d hd; cases hd)))
def cl_15319 : CNF.NClause := [(89,true),(14,true),(7,false),(16,true),(23,false),(27,false)]
theorem der_15319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15319 :=
  CNF.rup_sound cl_15319 [cl_14696,cl_1742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1742 v h) (by intro d hd; cases hd)))
def cl_15320 : CNF.NClause := [(89,true),(14,true),(7,true),(16,true),(23,false),(27,false)]
theorem der_15320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15320 :=
  CNF.rup_sound cl_15320 [cl_14696,cl_1744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1744 v h) (by intro d hd; cases hd)))
def cl_15321 : CNF.NClause := [(89,true),(23,true),(7,false),(14,false),(16,false),(27,false)]
theorem der_15321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15321 :=
  CNF.rup_sound cl_15321 [cl_14696,cl_1746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1746 v h) (by intro d hd; cases hd)))
def cl_15322 : CNF.NClause := [(89,true),(14,false),(16,false),(7,true),(23,true),(27,false)]
theorem der_15322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15322 :=
  CNF.rup_sound cl_15322 [cl_14696,cl_1748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1748 v h) (by intro d hd; cases hd)))
def cl_15323 : CNF.NClause := [(89,true),(14,true),(7,false),(16,false),(23,true),(27,false)]
theorem der_15323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15323 :=
  CNF.rup_sound cl_15323 [cl_14696,cl_1750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1750 v h) (by intro d hd; cases hd)))
def cl_15324 : CNF.NClause := [(89,true),(7,true),(16,false),(14,true),(23,true),(27,false)]
theorem der_15324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15324 :=
  CNF.rup_sound cl_15324 [cl_14696,cl_1752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1752 v h) (by intro d hd; cases hd)))
def cl_15325 : CNF.NClause := [(89,true),(14,false),(7,false),(16,true),(23,true),(27,false)]
theorem der_15325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15325 :=
  CNF.rup_sound cl_15325 [cl_14696,cl_1754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1754 v h) (by intro d hd; cases hd)))
def cl_15326 : CNF.NClause := [(89,true),(16,true),(7,true),(14,false),(23,true),(27,false)]
theorem der_15326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15326 :=
  CNF.rup_sound cl_15326 [cl_14696,cl_1756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1756 v h) (by intro d hd; cases hd)))
def cl_15327 : CNF.NClause := [(89,true),(14,true),(7,false),(16,true),(23,true),(27,false)]
theorem der_15327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15327 :=
  CNF.rup_sound cl_15327 [cl_14696,cl_1758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1758 v h) (by intro d hd; cases hd)))
def cl_15328 : CNF.NClause := [(89,false),(7,true),(14,true),(16,true),(23,true),(27,false)]
theorem der_15328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15328 :=
  CNF.rup_sound cl_15328 [cl_14696,cl_1760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1760 v h) (by intro d hd; cases hd)))
def cl_15329 : CNF.NClause := [(89,true),(23,false),(7,false),(14,false),(16,false),(27,true)]
theorem der_15329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15329 :=
  CNF.rup_sound cl_15329 [cl_14696,cl_1762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1762 v h) (by intro d hd; cases hd)))
def cl_15330 : CNF.NClause := [(89,true),(23,false),(7,true),(14,false),(16,false),(27,true)]
theorem der_15330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15330 :=
  CNF.rup_sound cl_15330 [cl_14696,cl_1764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1764 v h) (by intro d hd; cases hd)))
def cl_15331 : CNF.NClause := [(89,true),(14,true),(7,false),(16,false),(23,false),(27,true)]
theorem der_15331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15331 :=
  CNF.rup_sound cl_15331 [cl_14696,cl_1766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1766 v h) (by intro d hd; cases hd)))
def cl_15332 : CNF.NClause := [(89,true),(16,false),(14,true),(7,true),(23,false),(27,true)]
theorem der_15332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15332 :=
  CNF.rup_sound cl_15332 [cl_14696,cl_1768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1768 v h) (by intro d hd; cases hd)))
def cl_15333 : CNF.NClause := [(89,true),(14,false),(7,false),(16,true),(23,false),(27,true)]
theorem der_15333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15333 :=
  CNF.rup_sound cl_15333 [cl_14696,cl_1770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1770 v h) (by intro d hd; cases hd)))
def cl_15334 : CNF.NClause := [(89,true),(16,true),(7,true),(14,false),(23,false),(27,true)]
theorem der_15334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15334 :=
  CNF.rup_sound cl_15334 [cl_14696,cl_1772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1772 v h) (by intro d hd; cases hd)))
def cl_15335 : CNF.NClause := [(89,true),(14,true),(7,false),(16,true),(23,false),(27,true)]
theorem der_15335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15335 :=
  CNF.rup_sound cl_15335 [cl_14696,cl_1774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1774 v h) (by intro d hd; cases hd)))
def cl_15336 : CNF.NClause := [(89,false),(7,true),(14,true),(16,true),(23,false),(27,true)]
theorem der_15336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15336 :=
  CNF.rup_sound cl_15336 [cl_14696,cl_1776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1776 v h) (by intro d hd; cases hd)))
def cl_15337 : CNF.NClause := [(89,true),(23,true),(7,false),(14,false),(16,false),(27,true)]
theorem der_15337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15337 :=
  CNF.rup_sound cl_15337 [cl_14696,cl_1778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1778 v h) (by intro d hd; cases hd)))
def cl_15338 : CNF.NClause := [(89,true),(23,true),(7,true),(14,false),(16,false),(27,true)]
theorem der_15338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15338 :=
  CNF.rup_sound cl_15338 [cl_14696,cl_1780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1780 v h) (by intro d hd; cases hd)))
def cl_15339 : CNF.NClause := [(89,true),(14,true),(7,false),(16,false),(23,true),(27,true)]
theorem der_15339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15339 :=
  CNF.rup_sound cl_15339 [cl_14696,cl_1782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1782 v h) (by intro d hd; cases hd)))
def cl_15340 : CNF.NClause := [(89,false),(7,true),(14,true),(16,false),(23,true),(27,true)]
theorem der_15340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15340 :=
  CNF.rup_sound cl_15340 [cl_14696,cl_1784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1784 v h) (by intro d hd; cases hd)))
def cl_15341 : CNF.NClause := [(89,true),(14,false),(7,false),(16,true),(23,true),(27,true)]
theorem der_15341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15341 :=
  CNF.rup_sound cl_15341 [cl_14696,cl_1786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1786 v h) (by intro d hd; cases hd)))
def cl_15342 : CNF.NClause := [(89,false),(16,true),(7,true),(14,false),(23,true),(27,true)]
theorem der_15342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15342 :=
  CNF.rup_sound cl_15342 [cl_14696,cl_1788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1788 v h) (by intro d hd; cases hd)))
def cl_15343 : CNF.NClause := [(89,false),(7,false),(14,true),(16,true),(23,true),(27,true)]
theorem der_15343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15343 :=
  CNF.rup_sound cl_15343 [cl_14696,cl_1790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1790 v h) (by intro d hd; cases hd)))
def cl_15345 : CNF.NClause := [(90,true),(19,false),(8,false),(11,false),(22,false),(28,false)]
theorem der_15345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15345 :=
  CNF.rup_sound cl_15345 [cl_14696,cl_1794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1794 v h) (by intro d hd; cases hd)))
def cl_15346 : CNF.NClause := [(90,true),(19,false),(8,true),(11,false),(22,false),(28,false)]
theorem der_15346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15346 :=
  CNF.rup_sound cl_15346 [cl_14696,cl_1796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1796 v h) (by intro d hd; cases hd)))
def cl_15347 : CNF.NClause := [(90,true),(11,true),(8,false),(19,false),(22,false),(28,false)]
theorem der_15347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15347 :=
  CNF.rup_sound cl_15347 [cl_14696,cl_1798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1798 v h) (by intro d hd; cases hd)))
def cl_15348 : CNF.NClause := [(90,true),(11,true),(8,true),(19,false),(22,false),(28,false)]
theorem der_15348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15348 :=
  CNF.rup_sound cl_15348 [cl_14696,cl_1800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1800 v h) (by intro d hd; cases hd)))
def cl_15349 : CNF.NClause := [(90,true),(19,true),(11,false),(8,false),(22,false),(28,false)]
theorem der_15349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15349 :=
  CNF.rup_sound cl_15349 [cl_14696,cl_1802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1802 v h) (by intro d hd; cases hd)))
def cl_15350 : CNF.NClause := [(90,true),(8,true),(11,false),(19,true),(22,false),(28,false)]
theorem der_15350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15350 :=
  CNF.rup_sound cl_15350 [cl_14696,cl_1804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1804 v h) (by intro d hd; cases hd)))
def cl_15351 : CNF.NClause := [(90,true),(11,true),(8,false),(19,true),(22,false),(28,false)]
theorem der_15351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15351 :=
  CNF.rup_sound cl_15351 [cl_14696,cl_1806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1806 v h) (by intro d hd; cases hd)))
def cl_15352 : CNF.NClause := [(90,true),(11,true),(8,true),(19,true),(22,false),(28,false)]
theorem der_15352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15352 :=
  CNF.rup_sound cl_15352 [cl_14696,cl_1808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1808 v h) (by intro d hd; cases hd)))
def cl_15353 : CNF.NClause := [(90,true),(22,true),(8,false),(11,false),(19,false),(28,false)]
theorem der_15353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15353 :=
  CNF.rup_sound cl_15353 [cl_14696,cl_1810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1810 v h) (by intro d hd; cases hd)))
def cl_15354 : CNF.NClause := [(90,true),(19,false),(8,true),(11,false),(22,true),(28,false)]
theorem der_15354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15354 :=
  CNF.rup_sound cl_15354 [cl_14696,cl_1812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1812 v h) (by intro d hd; cases hd)))
def cl_15355 : CNF.NClause := [(90,true),(11,true),(8,false),(19,false),(22,true),(28,false)]
theorem der_15355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15355 :=
  CNF.rup_sound cl_15355 [cl_14696,cl_1814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1814 v h) (by intro d hd; cases hd)))
def cl_15356 : CNF.NClause := [(90,true),(11,true),(8,true),(19,false),(22,true),(28,false)]
theorem der_15356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15356 :=
  CNF.rup_sound cl_15356 [cl_14696,cl_1816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1816 v h) (by intro d hd; cases hd)))
def cl_15357 : CNF.NClause := [(90,true),(19,true),(11,false),(8,false),(22,true),(28,false)]
theorem der_15357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15357 :=
  CNF.rup_sound cl_15357 [cl_14696,cl_1818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1818 v h) (by intro d hd; cases hd)))
def cl_15358 : CNF.NClause := [(90,true),(8,true),(11,false),(19,true),(22,true),(28,false)]
theorem der_15358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15358 :=
  CNF.rup_sound cl_15358 [cl_14696,cl_1820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1820 v h) (by intro d hd; cases hd)))
def cl_15359 : CNF.NClause := [(90,true),(11,true),(8,false),(19,true),(22,true),(28,false)]
theorem der_15359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15359 :=
  CNF.rup_sound cl_15359 [cl_14696,cl_1822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1822 v h) (by intro d hd; cases hd)))
def cl_15360 : CNF.NClause := [(90,false),(11,true),(8,true),(19,true),(22,true),(28,false)]
theorem der_15360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15360 :=
  CNF.rup_sound cl_15360 [cl_14696,cl_1824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1824 v h) (by intro d hd; cases hd)))
def cl_15361 : CNF.NClause := [(90,true),(22,false),(8,false),(11,false),(19,false),(28,true)]
theorem der_15361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15361 :=
  CNF.rup_sound cl_15361 [cl_14696,cl_1826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1826 v h) (by intro d hd; cases hd)))
def cl_15362 : CNF.NClause := [(90,true),(19,false),(8,true),(11,false),(22,false),(28,true)]
theorem der_15362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15362 :=
  CNF.rup_sound cl_15362 [cl_14696,cl_1828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1828 v h) (by intro d hd; cases hd)))
def cl_15363 : CNF.NClause := [(90,true),(11,true),(8,false),(19,false),(22,false),(28,true)]
theorem der_15363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15363 :=
  CNF.rup_sound cl_15363 [cl_14696,cl_1830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1830 v h) (by intro d hd; cases hd)))
def cl_15364 : CNF.NClause := [(90,true),(11,true),(8,true),(19,false),(22,false),(28,true)]
theorem der_15364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15364 :=
  CNF.rup_sound cl_15364 [cl_14696,cl_1832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1832 v h) (by intro d hd; cases hd)))
def cl_15365 : CNF.NClause := [(90,true),(28,true),(8,false),(19,true),(22,false),(11,false)]
theorem der_15365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15365 :=
  CNF.rup_sound cl_15365 [cl_14696,cl_1834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1834 v h) (by intro d hd; cases hd)))
def cl_15366 : CNF.NClause := [(90,true),(28,true),(8,true),(19,true),(22,false),(11,false)]
theorem der_15366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15366 :=
  CNF.rup_sound cl_15366 [cl_14696,cl_1836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1836 v h) (by intro d hd; cases hd)))
def cl_15367 : CNF.NClause := [(90,true),(11,true),(8,false),(19,true),(22,false),(28,true)]
theorem der_15367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15367 :=
  CNF.rup_sound cl_15367 [cl_14696,cl_1838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1838 v h) (by intro d hd; cases hd)))
def cl_15368 : CNF.NClause := [(90,false),(11,true),(8,true),(19,true),(22,false),(28,true)]
theorem der_15368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15368 :=
  CNF.rup_sound cl_15368 [cl_14696,cl_1840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1840 v h) (by intro d hd; cases hd)))
def cl_15369 : CNF.NClause := [(90,true),(22,true),(8,false),(11,false),(19,false),(28,true)]
theorem der_15369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15369 :=
  CNF.rup_sound cl_15369 [cl_14696,cl_1842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1842 v h) (by intro d hd; cases hd)))
def cl_15370 : CNF.NClause := [(90,true),(19,false),(8,true),(11,false),(22,true),(28,true)]
theorem der_15370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15370 :=
  CNF.rup_sound cl_15370 [cl_14696,cl_1844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1844 v h) (by intro d hd; cases hd)))
def cl_15371 : CNF.NClause := [(90,true),(11,true),(8,false),(19,false),(22,true),(28,true)]
theorem der_15371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15371 :=
  CNF.rup_sound cl_15371 [cl_14696,cl_1846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1846 v h) (by intro d hd; cases hd)))
def cl_15372 : CNF.NClause := [(90,false),(22,true),(8,true),(11,true),(19,false),(28,true)]
theorem der_15372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15372 :=
  CNF.rup_sound cl_15372 [cl_14696,cl_1848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1848 v h) (by intro d hd; cases hd)))
def cl_15373 : CNF.NClause := [(90,true),(19,true),(11,false),(8,false),(22,true),(28,true)]
theorem der_15373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15373 :=
  CNF.rup_sound cl_15373 [cl_14696,cl_1850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1850 v h) (by intro d hd; cases hd)))
def cl_15374 : CNF.NClause := [(90,false),(8,true),(11,false),(19,true),(22,true),(28,true)]
theorem der_15374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15374 :=
  CNF.rup_sound cl_15374 [cl_14696,cl_1852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1852 v h) (by intro d hd; cases hd)))
def cl_15375 : CNF.NClause := [(90,false),(11,true),(8,false),(19,true),(22,true),(28,true)]
theorem der_15375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15375 :=
  CNF.rup_sound cl_15375 [cl_14696,cl_1854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1854 v h) (by intro d hd; cases hd)))
def cl_15377 : CNF.NClause := [(91,true),(18,false),(24,false),(6,false),(12,false),(26,false)]
theorem der_15377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15377 :=
  CNF.rup_sound cl_15377 [cl_14696,cl_1858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1858 v h) (by intro d hd; cases hd)))
def cl_15378 : CNF.NClause := [(91,true),(6,true),(12,false),(18,false),(24,false),(26,false)]
theorem der_15378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15378 :=
  CNF.rup_sound cl_15378 [cl_14696,cl_1860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1860 v h) (by intro d hd; cases hd)))
def cl_15379 : CNF.NClause := [(91,true),(12,true),(6,false),(18,false),(24,false),(26,false)]
theorem der_15379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15379 :=
  CNF.rup_sound cl_15379 [cl_14696,cl_1862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1862 v h) (by intro d hd; cases hd)))
def cl_15380 : CNF.NClause := [(91,true),(6,true),(18,false),(12,true),(24,false),(26,false)]
theorem der_15380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15380 :=
  CNF.rup_sound cl_15380 [cl_14696,cl_1864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1864 v h) (by intro d hd; cases hd)))
def cl_15381 : CNF.NClause := [(91,true),(18,true),(6,false),(12,false),(24,false),(26,false)]
theorem der_15381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15381 :=
  CNF.rup_sound cl_15381 [cl_14696,cl_1866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1866 v h) (by intro d hd; cases hd)))
def cl_15382 : CNF.NClause := [(91,true),(6,true),(12,false),(18,true),(24,false),(26,false)]
theorem der_15382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15382 :=
  CNF.rup_sound cl_15382 [cl_14696,cl_1868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1868 v h) (by intro d hd; cases hd)))
def cl_15383 : CNF.NClause := [(91,true),(18,true),(12,true),(6,false),(24,false),(26,false)]
theorem der_15383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15383 :=
  CNF.rup_sound cl_15383 [cl_14696,cl_1870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1870 v h) (by intro d hd; cases hd)))
def cl_15384 : CNF.NClause := [(91,true),(18,true),(6,true),(12,true),(24,false),(26,false)]
theorem der_15384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15384 :=
  CNF.rup_sound cl_15384 [cl_14696,cl_1872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1872 v h) (by intro d hd; cases hd)))
def cl_15385 : CNF.NClause := [(91,true),(24,true),(6,false),(12,false),(18,false),(26,false)]
theorem der_15385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15385 :=
  CNF.rup_sound cl_15385 [cl_14696,cl_1874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1874 v h) (by intro d hd; cases hd)))
def cl_15386 : CNF.NClause := [(91,true),(6,true),(12,false),(18,false),(24,true),(26,false)]
theorem der_15386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15386 :=
  CNF.rup_sound cl_15386 [cl_14696,cl_1876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1876 v h) (by intro d hd; cases hd)))
def cl_15387 : CNF.NClause := [(91,true),(24,true),(12,true),(18,false),(6,false),(26,false)]
theorem der_15387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15387 :=
  CNF.rup_sound cl_15387 [cl_14696,cl_1878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1878 v h) (by intro d hd; cases hd)))
def cl_15388 : CNF.NClause := [(91,true),(18,false),(6,true),(12,true),(24,true),(26,false)]
theorem der_15388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15388 :=
  CNF.rup_sound cl_15388 [cl_14696,cl_1880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1880 v h) (by intro d hd; cases hd)))
def cl_15389 : CNF.NClause := [(91,true),(18,true),(6,false),(12,false),(24,true),(26,false)]
theorem der_15389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15389 :=
  CNF.rup_sound cl_15389 [cl_14696,cl_1882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1882 v h) (by intro d hd; cases hd)))
def cl_15390 : CNF.NClause := [(91,true),(6,true),(12,false),(18,true),(24,true),(26,false)]
theorem der_15390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15390 :=
  CNF.rup_sound cl_15390 [cl_14696,cl_1884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1884 v h) (by intro d hd; cases hd)))
def cl_15391 : CNF.NClause := [(91,true),(18,true),(12,true),(6,false),(24,true),(26,false)]
theorem der_15391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15391 :=
  CNF.rup_sound cl_15391 [cl_14696,cl_1886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1886 v h) (by intro d hd; cases hd)))
def cl_15392 : CNF.NClause := [(91,false),(18,true),(6,true),(12,true),(24,true),(26,false)]
theorem der_15392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15392 :=
  CNF.rup_sound cl_15392 [cl_14696,cl_1888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1888 v h) (by intro d hd; cases hd)))
def cl_15393 : CNF.NClause := [(91,true),(18,false),(24,false),(6,false),(12,false),(26,true)]
theorem der_15393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15393 :=
  CNF.rup_sound cl_15393 [cl_14696,cl_1890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1890 v h) (by intro d hd; cases hd)))
def cl_15394 : CNF.NClause := [(91,true),(6,true),(12,false),(18,false),(24,false),(26,true)]
theorem der_15394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15394 :=
  CNF.rup_sound cl_15394 [cl_14696,cl_1892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1892 v h) (by intro d hd; cases hd)))
def cl_15395 : CNF.NClause := [(91,true),(12,true),(6,false),(18,false),(24,false),(26,true)]
theorem der_15395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15395 :=
  CNF.rup_sound cl_15395 [cl_14696,cl_1894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1894 v h) (by intro d hd; cases hd)))
def cl_15396 : CNF.NClause := [(91,true),(6,true),(18,false),(12,true),(24,false),(26,true)]
theorem der_15396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15396 :=
  CNF.rup_sound cl_15396 [cl_14696,cl_1896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1896 v h) (by intro d hd; cases hd)))
def cl_15397 : CNF.NClause := [(91,true),(18,true),(6,false),(12,false),(24,false),(26,true)]
theorem der_15397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15397 :=
  CNF.rup_sound cl_15397 [cl_14696,cl_1898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1898 v h) (by intro d hd; cases hd)))
def cl_15398 : CNF.NClause := [(91,true),(6,true),(12,false),(18,true),(24,false),(26,true)]
theorem der_15398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15398 :=
  CNF.rup_sound cl_15398 [cl_14696,cl_1900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1900 v h) (by intro d hd; cases hd)))
def cl_15399 : CNF.NClause := [(91,true),(12,true),(6,false),(18,true),(24,false),(26,true)]
theorem der_15399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15399 :=
  CNF.rup_sound cl_15399 [cl_14696,cl_1902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1902 v h) (by intro d hd; cases hd)))
def cl_15400 : CNF.NClause := [(91,false),(18,true),(6,true),(12,true),(24,false),(26,true)]
theorem der_15400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15400 :=
  CNF.rup_sound cl_15400 [cl_14696,cl_1904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1904 v h) (by intro d hd; cases hd)))
def cl_15401 : CNF.NClause := [(91,true),(24,true),(6,false),(12,false),(18,false),(26,true)]
theorem der_15401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15401 :=
  CNF.rup_sound cl_15401 [cl_14696,cl_1906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1906 v h) (by intro d hd; cases hd)))
def cl_15402 : CNF.NClause := [(91,true),(6,true),(12,false),(18,false),(24,true),(26,true)]
theorem der_15402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15402 :=
  CNF.rup_sound cl_15402 [cl_14696,cl_1908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1908 v h) (by intro d hd; cases hd)))
def cl_15403 : CNF.NClause := [(91,true),(12,true),(6,false),(18,false),(24,true),(26,true)]
theorem der_15403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15403 :=
  CNF.rup_sound cl_15403 [cl_14696,cl_1910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1910 v h) (by intro d hd; cases hd)))
def cl_15404 : CNF.NClause := [(91,false),(24,true),(6,true),(12,true),(18,false),(26,true)]
theorem der_15404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15404 :=
  CNF.rup_sound cl_15404 [cl_14696,cl_1912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1912 v h) (by intro d hd; cases hd)))
def cl_15405 : CNF.NClause := [(91,true),(18,true),(6,false),(12,false),(24,true),(26,true)]
theorem der_15405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15405 :=
  CNF.rup_sound cl_15405 [cl_14696,cl_1914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1914 v h) (by intro d hd; cases hd)))
def cl_15406 : CNF.NClause := [(91,false),(6,true),(12,false),(18,true),(24,true),(26,true)]
theorem der_15406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15406 :=
  CNF.rup_sound cl_15406 [cl_14696,cl_1916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1916 v h) (by intro d hd; cases hd)))
def cl_15407 : CNF.NClause := [(91,false),(18,true),(12,true),(6,false),(24,true),(26,true)]
theorem der_15407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15407 :=
  CNF.rup_sound cl_15407 [cl_14696,cl_1918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1918 v h) (by intro d hd; cases hd)))
def cl_15408 : CNF.NClause := [(91,false),(18,true),(6,true),(12,true),(24,true),(26,true)]
theorem der_15408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15408 :=
  CNF.rup_sound cl_15408 [cl_14696,cl_1920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_1920 v h) (by intro d hd; cases hd)))
def cl_15409 : CNF.NClause := [(92,true),(10,false),(15,false),(5,false),(20,false)]
theorem der_15409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15409 :=
  CNF.rup_sound cl_15409 [cl_14696,cl_14697,cl_1954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1954 v h) (by intro d hd; cases hd))))
def cl_15410 : CNF.NClause := [(92,true),(5,true),(10,false),(15,false),(20,false)]
theorem der_15410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15410 :=
  CNF.rup_sound cl_15410 [cl_14696,cl_14697,cl_1956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1956 v h) (by intro d hd; cases hd))))
def cl_15411 : CNF.NClause := [(92,true),(10,true),(5,false),(15,false),(20,false)]
theorem der_15411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15411 :=
  CNF.rup_sound cl_15411 [cl_14696,cl_14697,cl_1958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1958 v h) (by intro d hd; cases hd))))
def cl_15412 : CNF.NClause := [(92,true),(10,true),(5,true),(15,false),(20,false)]
theorem der_15412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15412 :=
  CNF.rup_sound cl_15412 [cl_14696,cl_14697,cl_1960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1960 v h) (by intro d hd; cases hd))))
def cl_15413 : CNF.NClause := [(92,true),(15,true),(5,false),(10,false),(20,false)]
theorem der_15413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15413 :=
  CNF.rup_sound cl_15413 [cl_14696,cl_14697,cl_1962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1962 v h) (by intro d hd; cases hd))))
def cl_15414 : CNF.NClause := [(92,true),(5,true),(10,false),(15,true),(20,false)]
theorem der_15414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15414 :=
  CNF.rup_sound cl_15414 [cl_14696,cl_14697,cl_1964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1964 v h) (by intro d hd; cases hd))))
def cl_15415 : CNF.NClause := [(92,true),(10,true),(5,false),(15,true),(20,false)]
theorem der_15415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15415 :=
  CNF.rup_sound cl_15415 [cl_14696,cl_14697,cl_1966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1966 v h) (by intro d hd; cases hd))))
def cl_15416 : CNF.NClause := [(92,false),(15,true),(5,true),(10,true),(20,false)]
theorem der_15416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15416 :=
  CNF.rup_sound cl_15416 [cl_14696,cl_14697,cl_1968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1968 v h) (by intro d hd; cases hd))))
def cl_15417 : CNF.NClause := [(92,true),(20,true),(5,false),(10,false),(15,false)]
theorem der_15417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15417 :=
  CNF.rup_sound cl_15417 [cl_14696,cl_14697,cl_1970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1970 v h) (by intro d hd; cases hd))))
def cl_15418 : CNF.NClause := [(92,true),(5,true),(10,false),(15,false),(20,true)]
theorem der_15418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15418 :=
  CNF.rup_sound cl_15418 [cl_14696,cl_14697,cl_1972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1972 v h) (by intro d hd; cases hd))))
def cl_15419 : CNF.NClause := [(92,true),(10,true),(5,false),(15,false),(20,true)]
theorem der_15419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15419 :=
  CNF.rup_sound cl_15419 [cl_14696,cl_14697,cl_1974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1974 v h) (by intro d hd; cases hd))))
def cl_15420 : CNF.NClause := [(92,false),(10,true),(5,true),(15,false),(20,true)]
theorem der_15420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15420 :=
  CNF.rup_sound cl_15420 [cl_14696,cl_14697,cl_1976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1976 v h) (by intro d hd; cases hd))))
def cl_15421 : CNF.NClause := [(92,true),(15,true),(5,false),(10,false),(20,true)]
theorem der_15421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15421 :=
  CNF.rup_sound cl_15421 [cl_14696,cl_14697,cl_1978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1978 v h) (by intro d hd; cases hd))))
def cl_15422 : CNF.NClause := [(92,false),(5,true),(10,false),(15,true),(20,true)]
theorem der_15422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15422 :=
  CNF.rup_sound cl_15422 [cl_14696,cl_14697,cl_1980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1980 v h) (by intro d hd; cases hd))))
def cl_15423 : CNF.NClause := [(92,false),(10,true),(5,false),(15,true),(20,true)]
theorem der_15423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15423 :=
  CNF.rup_sound cl_15423 [cl_14696,cl_14697,cl_1982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_1982 v h) (by intro d hd; cases hd))))
def cl_15425 : CNF.NClause := [(31,false),(88,false),(87,false),(91,false),(89,false),(90,false),(92,false)]
theorem der_15425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15425 :=
  CNF.rup_sound cl_15425 [cl_14696,cl_3970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3970 v h) (by intro d hd; cases hd)))
def cl_15426 : CNF.NClause := [(31,false),(87,true),(89,false),(88,false),(90,false),(91,false),(92,false)]
theorem der_15426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15426 :=
  CNF.rup_sound cl_15426 [cl_14696,cl_3972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3972 v h) (by intro d hd; cases hd)))
def cl_15427 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,false),(91,false),(92,false)]
theorem der_15427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15427 :=
  CNF.rup_sound cl_15427 [cl_14696,cl_3974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3974 v h) (by intro d hd; cases hd)))
def cl_15428 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,false),(91,false),(92,false)]
theorem der_15428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15428 :=
  CNF.rup_sound cl_15428 [cl_14696,cl_3976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3976 v h) (by intro d hd; cases hd)))
def cl_15429 : CNF.NClause := [(31,false),(89,true),(87,false),(91,false),(88,false),(90,false),(92,false)]
theorem der_15429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15429 :=
  CNF.rup_sound cl_15429 [cl_14696,cl_3978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3978 v h) (by intro d hd; cases hd)))
def cl_15430 : CNF.NClause := [(31,false),(91,false),(87,true),(89,true),(88,false),(90,false),(92,false)]
theorem der_15430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15430 :=
  CNF.rup_sound cl_15430 [cl_14696,cl_3980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3980 v h) (by intro d hd; cases hd)))
def cl_15431 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,false),(91,false),(92,false)]
theorem der_15431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15431 :=
  CNF.rup_sound cl_15431 [cl_14696,cl_3982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3982 v h) (by intro d hd; cases hd)))
def cl_15432 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,false),(91,false),(92,false)]
theorem der_15432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15432 :=
  CNF.rup_sound cl_15432 [cl_14696,cl_3984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3984 v h) (by intro d hd; cases hd)))
def cl_15433 : CNF.NClause := [(31,false),(90,true),(87,false),(88,false),(89,false),(91,false),(92,false)]
theorem der_15433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15433 :=
  CNF.rup_sound cl_15433 [cl_14696,cl_3986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3986 v h) (by intro d hd; cases hd)))
def cl_15434 : CNF.NClause := [(31,false),(90,true),(87,true),(88,false),(89,false),(91,false),(92,false)]
theorem der_15434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15434 :=
  CNF.rup_sound cl_15434 [cl_14696,cl_3988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3988 v h) (by intro d hd; cases hd)))
def cl_15435 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,true),(91,false),(92,false)]
theorem der_15435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15435 :=
  CNF.rup_sound cl_15435 [cl_14696,cl_3990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3990 v h) (by intro d hd; cases hd)))
def cl_15436 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,true),(91,false),(92,false)]
theorem der_15436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15436 :=
  CNF.rup_sound cl_15436 [cl_14696,cl_3992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3992 v h) (by intro d hd; cases hd)))
def cl_15437 : CNF.NClause := [(31,false),(89,true),(87,false),(88,false),(90,true),(91,false),(92,false)]
theorem der_15437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15437 :=
  CNF.rup_sound cl_15437 [cl_14696,cl_3994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3994 v h) (by intro d hd; cases hd)))
def cl_15438 : CNF.NClause := [(31,false),(87,true),(88,false),(89,true),(90,true),(91,false),(92,false)]
theorem der_15438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15438 :=
  CNF.rup_sound cl_15438 [cl_14696,cl_3996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3996 v h) (by intro d hd; cases hd)))
def cl_15439 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,true),(91,false),(92,false)]
theorem der_15439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15439 :=
  CNF.rup_sound cl_15439 [cl_14696,cl_3998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_3998 v h) (by intro d hd; cases hd)))
def cl_15440 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,true),(91,false),(92,false)]
theorem der_15440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15440 :=
  CNF.rup_sound cl_15440 [cl_14696,cl_4000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4000 v h) (by intro d hd; cases hd)))
def cl_15441 : CNF.NClause := [(31,false),(91,true),(87,false),(88,false),(89,false),(90,false),(92,false)]
theorem der_15441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15441 :=
  CNF.rup_sound cl_15441 [cl_14696,cl_4002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4002 v h) (by intro d hd; cases hd)))
def cl_15442 : CNF.NClause := [(31,false),(91,true),(87,true),(88,false),(90,false),(89,false),(92,false)]
theorem der_15442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15442 :=
  CNF.rup_sound cl_15442 [cl_14696,cl_4004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4004 v h) (by intro d hd; cases hd)))
def cl_15443 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,false),(91,true),(92,false)]
theorem der_15443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15443 :=
  CNF.rup_sound cl_15443 [cl_14696,cl_4006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4006 v h) (by intro d hd; cases hd)))
def cl_15444 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,false),(91,true),(92,false)]
theorem der_15444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15444 :=
  CNF.rup_sound cl_15444 [cl_14696,cl_4008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4008 v h) (by intro d hd; cases hd)))
def cl_15445 : CNF.NClause := [(31,false),(89,true),(87,false),(88,false),(90,false),(91,true),(92,false)]
theorem der_15445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15445 :=
  CNF.rup_sound cl_15445 [cl_14696,cl_4010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4010 v h) (by intro d hd; cases hd)))
def cl_15446 : CNF.NClause := [(31,false),(91,true),(87,true),(89,true),(88,false),(90,false),(92,false)]
theorem der_15446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15446 :=
  CNF.rup_sound cl_15446 [cl_14696,cl_4012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4012 v h) (by intro d hd; cases hd)))
def cl_15447 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,false),(91,true),(92,false)]
theorem der_15447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15447 :=
  CNF.rup_sound cl_15447 [cl_14696,cl_4014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4014 v h) (by intro d hd; cases hd)))
def cl_15448 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,false),(91,true),(92,false)]
theorem der_15448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15448 :=
  CNF.rup_sound cl_15448 [cl_14696,cl_4016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4016 v h) (by intro d hd; cases hd)))
def cl_15449 : CNF.NClause := [(31,false),(90,true),(87,false),(88,false),(89,false),(91,true),(92,false)]
theorem der_15449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15449 :=
  CNF.rup_sound cl_15449 [cl_14696,cl_4018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4018 v h) (by intro d hd; cases hd)))
def cl_15450 : CNF.NClause := [(31,false),(90,true),(87,true),(88,false),(89,false),(91,true),(92,false)]
theorem der_15450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15450 :=
  CNF.rup_sound cl_15450 [cl_14696,cl_4020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4020 v h) (by intro d hd; cases hd)))
def cl_15451 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,true),(91,true),(92,false)]
theorem der_15451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15451 :=
  CNF.rup_sound cl_15451 [cl_14696,cl_4022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4022 v h) (by intro d hd; cases hd)))
def cl_15452 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,true),(91,true),(92,false)]
theorem der_15452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15452 :=
  CNF.rup_sound cl_15452 [cl_14696,cl_4024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4024 v h) (by intro d hd; cases hd)))
def cl_15453 : CNF.NClause := [(31,false),(89,true),(87,false),(88,false),(90,true),(91,true),(92,false)]
theorem der_15453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15453 :=
  CNF.rup_sound cl_15453 [cl_14696,cl_4026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4026 v h) (by intro d hd; cases hd)))
def cl_15454 : CNF.NClause := [(31,false),(91,true),(87,true),(89,true),(90,true),(88,false),(92,false)]
theorem der_15454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15454 :=
  CNF.rup_sound cl_15454 [cl_14696,cl_4028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4028 v h) (by intro d hd; cases hd)))
def cl_15455 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,true),(91,true),(92,false)]
theorem der_15455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15455 :=
  CNF.rup_sound cl_15455 [cl_14696,cl_4030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4030 v h) (by intro d hd; cases hd)))
def cl_15456 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,true),(91,true),(92,false)]
theorem der_15456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15456 :=
  CNF.rup_sound cl_15456 [cl_14696,cl_4032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4032 v h) (by intro d hd; cases hd)))
def cl_15457 : CNF.NClause := [(31,false),(91,false),(87,false),(88,false),(89,false),(90,false),(92,true)]
theorem der_15457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15457 :=
  CNF.rup_sound cl_15457 [cl_14696,cl_4034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4034 v h) (by intro d hd; cases hd)))
def cl_15458 : CNF.NClause := [(31,false),(92,true),(87,true),(88,false),(90,false),(89,false),(91,false)]
theorem der_15458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15458 :=
  CNF.rup_sound cl_15458 [cl_14696,cl_4036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4036 v h) (by intro d hd; cases hd)))
def cl_15459 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,false),(91,false),(92,true)]
theorem der_15459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15459 :=
  CNF.rup_sound cl_15459 [cl_14696,cl_4038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4038 v h) (by intro d hd; cases hd)))
def cl_15460 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,false),(91,false),(92,true)]
theorem der_15460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15460 :=
  CNF.rup_sound cl_15460 [cl_14696,cl_4040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4040 v h) (by intro d hd; cases hd)))
def cl_15461 : CNF.NClause := [(31,false),(89,true),(87,false),(88,false),(90,false),(91,false),(92,true)]
theorem der_15461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15461 :=
  CNF.rup_sound cl_15461 [cl_14696,cl_4042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4042 v h) (by intro d hd; cases hd)))
def cl_15462 : CNF.NClause := [(31,false),(91,false),(87,true),(89,true),(88,false),(90,false),(92,true)]
theorem der_15462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15462 :=
  CNF.rup_sound cl_15462 [cl_14696,cl_4044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4044 v h) (by intro d hd; cases hd)))
def cl_15463 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,false),(91,false),(92,true)]
theorem der_15463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15463 :=
  CNF.rup_sound cl_15463 [cl_14696,cl_4046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4046 v h) (by intro d hd; cases hd)))
def cl_15464 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,false),(91,false),(92,true)]
theorem der_15464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15464 :=
  CNF.rup_sound cl_15464 [cl_14696,cl_4048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4048 v h) (by intro d hd; cases hd)))
def cl_15465 : CNF.NClause := [(31,false),(90,true),(87,false),(88,false),(89,false),(91,false),(92,true)]
theorem der_15465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15465 :=
  CNF.rup_sound cl_15465 [cl_14696,cl_4050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4050 v h) (by intro d hd; cases hd)))
def cl_15466 : CNF.NClause := [(31,false),(90,true),(87,true),(88,false),(89,false),(91,false),(92,true)]
theorem der_15466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15466 :=
  CNF.rup_sound cl_15466 [cl_14696,cl_4052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4052 v h) (by intro d hd; cases hd)))
def cl_15467 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,true),(91,false),(92,true)]
theorem der_15467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15467 :=
  CNF.rup_sound cl_15467 [cl_14696,cl_4054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4054 v h) (by intro d hd; cases hd)))
def cl_15468 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,true),(91,false),(92,true)]
theorem der_15468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15468 :=
  CNF.rup_sound cl_15468 [cl_14696,cl_4056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4056 v h) (by intro d hd; cases hd)))
def cl_15469 : CNF.NClause := [(31,false),(89,true),(87,false),(88,false),(90,true),(91,false),(92,true)]
theorem der_15469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15469 :=
  CNF.rup_sound cl_15469 [cl_14696,cl_4058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4058 v h) (by intro d hd; cases hd)))
def cl_15470 : CNF.NClause := [(31,false),(92,true),(87,true),(89,true),(90,true),(91,false),(88,false)]
theorem der_15470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15470 :=
  CNF.rup_sound cl_15470 [cl_14696,cl_4060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4060 v h) (by intro d hd; cases hd)))
def cl_15471 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,true),(91,false),(92,true)]
theorem der_15471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15471 :=
  CNF.rup_sound cl_15471 [cl_14696,cl_4062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4062 v h) (by intro d hd; cases hd)))
def cl_15472 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,true),(91,false),(92,true)]
theorem der_15472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15472 :=
  CNF.rup_sound cl_15472 [cl_14696,cl_4064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4064 v h) (by intro d hd; cases hd)))
def cl_15473 : CNF.NClause := [(31,false),(91,true),(87,false),(88,false),(89,false),(90,false),(92,true)]
theorem der_15473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15473 :=
  CNF.rup_sound cl_15473 [cl_14696,cl_4066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4066 v h) (by intro d hd; cases hd)))
def cl_15474 : CNF.NClause := [(31,false),(91,true),(87,true),(88,false),(90,false),(89,false),(92,true)]
theorem der_15474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15474 :=
  CNF.rup_sound cl_15474 [cl_14696,cl_4068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4068 v h) (by intro d hd; cases hd)))
def cl_15475 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,false),(91,true),(92,true)]
theorem der_15475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15475 :=
  CNF.rup_sound cl_15475 [cl_14696,cl_4070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4070 v h) (by intro d hd; cases hd)))
def cl_15476 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,false),(91,true),(92,true)]
theorem der_15476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15476 :=
  CNF.rup_sound cl_15476 [cl_14696,cl_4072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4072 v h) (by intro d hd; cases hd)))
def cl_15477 : CNF.NClause := [(31,false),(89,true),(87,false),(88,false),(90,false),(91,true),(92,true)]
theorem der_15477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15477 :=
  CNF.rup_sound cl_15477 [cl_14696,cl_4074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4074 v h) (by intro d hd; cases hd)))
def cl_15478 : CNF.NClause := [(31,false),(91,true),(87,true),(89,true),(88,false),(90,false),(92,true)]
theorem der_15478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15478 :=
  CNF.rup_sound cl_15478 [cl_14696,cl_4076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4076 v h) (by intro d hd; cases hd)))
def cl_15479 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,false),(91,true),(92,true)]
theorem der_15479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15479 :=
  CNF.rup_sound cl_15479 [cl_14696,cl_4078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4078 v h) (by intro d hd; cases hd)))
def cl_15480 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,false),(91,true),(92,true)]
theorem der_15480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15480 :=
  CNF.rup_sound cl_15480 [cl_14696,cl_4080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4080 v h) (by intro d hd; cases hd)))
def cl_15481 : CNF.NClause := [(31,false),(90,true),(87,false),(88,false),(89,false),(91,true),(92,true)]
theorem der_15481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15481 :=
  CNF.rup_sound cl_15481 [cl_14696,cl_4082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4082 v h) (by intro d hd; cases hd)))
def cl_15482 : CNF.NClause := [(31,false),(90,true),(87,true),(88,false),(89,false),(91,true),(92,true)]
theorem der_15482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15482 :=
  CNF.rup_sound cl_15482 [cl_14696,cl_4084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4084 v h) (by intro d hd; cases hd)))
def cl_15483 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(90,true),(91,true),(92,true)]
theorem der_15483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15483 :=
  CNF.rup_sound cl_15483 [cl_14696,cl_4086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4086 v h) (by intro d hd; cases hd)))
def cl_15484 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,true),(91,true),(92,true)]
theorem der_15484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15484 :=
  CNF.rup_sound cl_15484 [cl_14696,cl_4088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4088 v h) (by intro d hd; cases hd)))
def cl_15485 : CNF.NClause := [(31,false),(89,true),(87,false),(88,false),(90,true),(91,true),(92,true)]
theorem der_15485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15485 :=
  CNF.rup_sound cl_15485 [cl_14696,cl_4090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4090 v h) (by intro d hd; cases hd)))
def cl_15486 : CNF.NClause := [(31,false),(91,true),(87,true),(89,true),(90,true),(88,false),(92,true)]
theorem der_15486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15486 :=
  CNF.rup_sound cl_15486 [cl_14696,cl_4092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4092 v h) (by intro d hd; cases hd)))
def cl_15487 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,true),(91,true),(92,true)]
theorem der_15487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15487 :=
  CNF.rup_sound cl_15487 [cl_14696,cl_4094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4094 v h) (by intro d hd; cases hd)))
def cl_15488 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,true),(91,true),(92,true)]
theorem der_15488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15488 :=
  CNF.rup_sound cl_15488 [cl_14696,cl_4096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14696 v h) (hints_cons _ _ _ (inp_4096 v h) (by intro d hd; cases hd)))
def cl_15489 : CNF.NClause := [(56,false),(65,false),(66,false),(63,false),(64,false),(62,false),(92,false)]
theorem der_15489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15489 :=
  CNF.rup_sound cl_15489 [cl_14697,cl_7170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7170 v h) (by intro d hd; cases hd)))
def cl_15490 : CNF.NClause := [(56,false),(63,false),(62,true),(64,false),(65,false),(66,false),(92,false)]
theorem der_15490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15490 :=
  CNF.rup_sound cl_15490 [cl_14697,cl_7172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14697 v h) (hints_cons _ _ _ (inp_7172 v h) (by intro d hd; cases hd)))
def chunk000 : List CNF.NClause := [cl_14699,cl_14700,cl_14701,cl_14702,cl_14703,cl_14704,cl_14705,cl_14706,cl_14707,cl_14710,cl_14712,cl_14714,cl_14716,cl_14718,cl_14720,cl_14722,cl_14729,cl_14736,cl_15001,cl_15002,cl_15003,cl_15004,cl_15005,cl_15006,cl_15007,cl_15008,cl_15009,cl_15010,cl_15011,cl_15012,cl_15013,cl_15014,cl_15015,cl_15017,cl_15018,cl_15019,cl_15020,cl_15021,cl_15022,cl_15023,cl_15024,cl_15025,cl_15026,cl_15027,cl_15028,cl_15029,cl_15030,cl_15031,cl_15032,cl_15033,cl_15034,cl_15035,cl_15036,cl_15037,cl_15038,cl_15039,cl_15040,cl_15041,cl_15042,cl_15043,cl_15044,cl_15045,cl_15046,cl_15047,cl_15048,cl_15049,cl_15050,cl_15051,cl_15052,cl_15053,cl_15054,cl_15055,cl_15056,cl_15057,cl_15058,cl_15059,cl_15060,cl_15061,cl_15062,cl_15063,cl_15064,cl_15065,cl_15066,cl_15067,cl_15068,cl_15069,cl_15070,cl_15071,cl_15072,cl_15073,cl_15074,cl_15075,cl_15076,cl_15077,cl_15078,cl_15079,cl_15080,cl_15081,cl_15082,cl_15083,cl_15084,cl_15085,cl_15086,cl_15087,cl_15088,cl_15089,cl_15090,cl_15091,cl_15092,cl_15093,cl_15094,cl_15095,cl_15096,cl_15097,cl_15098,cl_15099,cl_15100,cl_15101,cl_15102,cl_15103,cl_15104,cl_15105,cl_15106,cl_15107,cl_15108,cl_15109,cl_15110,cl_15111,cl_15112,cl_15113,cl_15114,cl_15115,cl_15116,cl_15117,cl_15118,cl_15119,cl_15120,cl_15121,cl_15122,cl_15123,cl_15124,cl_15125,cl_15126,cl_15127,cl_15128,cl_15129,cl_15130,cl_15131,cl_15132,cl_15133,cl_15134,cl_15135,cl_15136,cl_15137,cl_15138,cl_15139,cl_15140,cl_15141,cl_15142,cl_15143,cl_15144,cl_15145,cl_15146,cl_15147,cl_15148,cl_15149,cl_15150,cl_15151,cl_15152,cl_15153,cl_15154,cl_15155,cl_15156,cl_15157,cl_15158,cl_15159,cl_15160,cl_15161,cl_15162,cl_15163,cl_15164,cl_15165,cl_15166,cl_15167,cl_15168,cl_15169,cl_15170,cl_15171,cl_15172,cl_15173,cl_15175,cl_15176,cl_15177,cl_15178,cl_15179,cl_15180,cl_15181,cl_15182,cl_15183,cl_15184,cl_15185,cl_15186,cl_15187,cl_15188,cl_15189,cl_15190,cl_15191,cl_15192,cl_15193,cl_15194,cl_15195,cl_15196,cl_15197,cl_15198,cl_15199,cl_15200,cl_15201,cl_15202,cl_15203,cl_15204,cl_15205,cl_15206,cl_15207,cl_15208,cl_15209,cl_15210,cl_15211,cl_15212,cl_15213,cl_15214,cl_15215,cl_15216,cl_15217,cl_15218,cl_15219,cl_15220,cl_15221,cl_15222,cl_15223,cl_15224,cl_15225,cl_15226,cl_15227,cl_15228,cl_15229,cl_15230,cl_15231,cl_15232,cl_15233,cl_15234,cl_15235,cl_15236,cl_15237,cl_15238,cl_15239,cl_15240,cl_15241,cl_15242,cl_15243,cl_15244,cl_15245,cl_15246,cl_15247,cl_15248,cl_15249,cl_15250,cl_15251,cl_15252,cl_15253,cl_15254,cl_15255,cl_15256,cl_15257,cl_15258,cl_15259,cl_15260,cl_15261,cl_15262,cl_15263,cl_15264,cl_15265,cl_15267,cl_15268,cl_15269,cl_15270,cl_15271,cl_15272,cl_15273,cl_15274,cl_15275,cl_15276,cl_15277,cl_15278,cl_15279,cl_15280,cl_15281,cl_15283,cl_15284,cl_15285,cl_15286,cl_15287,cl_15288,cl_15289,cl_15290,cl_15291,cl_15292,cl_15293,cl_15294,cl_15295,cl_15296,cl_15297,cl_15298,cl_15299,cl_15300,cl_15301,cl_15302,cl_15303,cl_15304,cl_15305,cl_15306,cl_15307,cl_15308,cl_15309,cl_15310,cl_15311,cl_15312,cl_15313,cl_15315,cl_15316,cl_15317,cl_15318,cl_15319,cl_15320,cl_15321,cl_15322,cl_15323,cl_15324,cl_15325,cl_15326,cl_15327,cl_15328,cl_15329,cl_15330,cl_15331,cl_15332,cl_15333,cl_15334,cl_15335,cl_15336,cl_15337,cl_15338,cl_15339,cl_15340,cl_15341,cl_15342,cl_15343,cl_15345,cl_15346,cl_15347,cl_15348,cl_15349,cl_15350,cl_15351,cl_15352,cl_15353,cl_15354,cl_15355,cl_15356,cl_15357,cl_15358,cl_15359,cl_15360,cl_15361,cl_15362,cl_15363,cl_15364,cl_15365,cl_15366,cl_15367,cl_15368,cl_15369,cl_15370,cl_15371,cl_15372,cl_15373,cl_15374,cl_15375,cl_15377,cl_15378,cl_15379,cl_15380,cl_15381,cl_15382,cl_15383,cl_15384,cl_15385,cl_15386,cl_15387,cl_15388,cl_15389,cl_15390,cl_15391,cl_15392,cl_15393,cl_15394,cl_15395,cl_15396,cl_15397,cl_15398,cl_15399,cl_15400,cl_15401,cl_15402,cl_15403,cl_15404,cl_15405,cl_15406,cl_15407,cl_15408,cl_15409,cl_15410,cl_15411,cl_15412,cl_15413,cl_15414,cl_15415,cl_15416,cl_15417,cl_15418,cl_15419,cl_15420,cl_15421,cl_15422,cl_15423,cl_15425,cl_15426,cl_15427,cl_15428,cl_15429,cl_15430,cl_15431,cl_15432,cl_15433,cl_15434,cl_15435,cl_15436,cl_15437,cl_15438,cl_15439,cl_15440,cl_15441,cl_15442,cl_15443,cl_15444,cl_15445,cl_15446,cl_15447,cl_15448,cl_15449,cl_15450,cl_15451,cl_15452,cl_15453,cl_15454,cl_15455,cl_15456,cl_15457,cl_15458,cl_15459,cl_15460,cl_15461,cl_15462,cl_15463,cl_15464,cl_15465,cl_15466,cl_15467,cl_15468,cl_15469,cl_15470,cl_15471,cl_15472,cl_15473,cl_15474,cl_15475,cl_15476,cl_15477,cl_15478,cl_15479,cl_15480,cl_15481,cl_15482,cl_15483,cl_15484,cl_15485,cl_15486,cl_15487,cl_15488,cl_15489,cl_15490]
theorem chunk_sound000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk000, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_14699 v h) (hints_cons _ _ _ (der_14700 v h) (hints_cons _ _ _ (der_14701 v h) (hints_cons _ _ _ (der_14702 v h) (hints_cons _ _ _ (der_14703 v h) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (der_14705 v h) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (der_14707 v h) (hints_cons _ _ _ (der_14710 v h) (hints_cons _ _ _ (der_14712 v h) (hints_cons _ _ _ (der_14714 v h) (hints_cons _ _ _ (der_14716 v h) (hints_cons _ _ _ (der_14718 v h) (hints_cons _ _ _ (der_14720 v h) (hints_cons _ _ _ (der_14722 v h) (hints_cons _ _ _ (der_14729 v h) (hints_cons _ _ _ (der_14736 v h) (hints_cons _ _ _ (der_15001 v h) (hints_cons _ _ _ (der_15002 v h) (hints_cons _ _ _ (der_15003 v h) (hints_cons _ _ _ (der_15004 v h) (hints_cons _ _ _ (der_15005 v h) (hints_cons _ _ _ (der_15006 v h) (hints_cons _ _ _ (der_15007 v h) (hints_cons _ _ _ (der_15008 v h) (hints_cons _ _ _ (der_15009 v h) (hints_cons _ _ _ (der_15010 v h) (hints_cons _ _ _ (der_15011 v h) (hints_cons _ _ _ (der_15012 v h) (hints_cons _ _ _ (der_15013 v h) (hints_cons _ _ _ (der_15014 v h) (hints_cons _ _ _ (der_15015 v h) (hints_cons _ _ _ (der_15017 v h) (hints_cons _ _ _ (der_15018 v h) (hints_cons _ _ _ (der_15019 v h) (hints_cons _ _ _ (der_15020 v h) (hints_cons _ _ _ (der_15021 v h) (hints_cons _ _ _ (der_15022 v h) (hints_cons _ _ _ (der_15023 v h) (hints_cons _ _ _ (der_15024 v h) (hints_cons _ _ _ (der_15025 v h) (hints_cons _ _ _ (der_15026 v h) (hints_cons _ _ _ (der_15027 v h) (hints_cons _ _ _ (der_15028 v h) (hints_cons _ _ _ (der_15029 v h) (hints_cons _ _ _ (der_15030 v h) (hints_cons _ _ _ (der_15031 v h) (hints_cons _ _ _ (der_15032 v h) (hints_cons _ _ _ (der_15033 v h) (hints_cons _ _ _ (der_15034 v h) (hints_cons _ _ _ (der_15035 v h) (hints_cons _ _ _ (der_15036 v h) (hints_cons _ _ _ (der_15037 v h) (hints_cons _ _ _ (der_15038 v h) (hints_cons _ _ _ (der_15039 v h) (hints_cons _ _ _ (der_15040 v h) (hints_cons _ _ _ (der_15041 v h) (hints_cons _ _ _ (der_15042 v h) (hints_cons _ _ _ (der_15043 v h) (hints_cons _ _ _ (der_15044 v h) (hints_cons _ _ _ (der_15045 v h) (hints_cons _ _ _ (der_15046 v h) (hints_cons _ _ _ (der_15047 v h) (hints_cons _ _ _ (der_15048 v h) (hints_cons _ _ _ (der_15049 v h) (hints_cons _ _ _ (der_15050 v h) (hints_cons _ _ _ (der_15051 v h) (hints_cons _ _ _ (der_15052 v h) (hints_cons _ _ _ (der_15053 v h) (hints_cons _ _ _ (der_15054 v h) (hints_cons _ _ _ (der_15055 v h) (hints_cons _ _ _ (der_15056 v h) (hints_cons _ _ _ (der_15057 v h) (hints_cons _ _ _ (der_15058 v h) (hints_cons _ _ _ (der_15059 v h) (hints_cons _ _ _ (der_15060 v h) (hints_cons _ _ _ (der_15061 v h) (hints_cons _ _ _ (der_15062 v h) (hints_cons _ _ _ (der_15063 v h) (hints_cons _ _ _ (der_15064 v h) (hints_cons _ _ _ (der_15065 v h) (hints_cons _ _ _ (der_15066 v h) (hints_cons _ _ _ (der_15067 v h) (hints_cons _ _ _ (der_15068 v h) (hints_cons _ _ _ (der_15069 v h) (hints_cons _ _ _ (der_15070 v h) (hints_cons _ _ _ (der_15071 v h) (hints_cons _ _ _ (der_15072 v h) (hints_cons _ _ _ (der_15073 v h) (hints_cons _ _ _ (der_15074 v h) (hints_cons _ _ _ (der_15075 v h) (hints_cons _ _ _ (der_15076 v h) (hints_cons _ _ _ (der_15077 v h) (hints_cons _ _ _ (der_15078 v h) (hints_cons _ _ _ (der_15079 v h) (hints_cons _ _ _ (der_15080 v h) (hints_cons _ _ _ (der_15081 v h) (hints_cons _ _ _ (der_15082 v h) (hints_cons _ _ _ (der_15083 v h) (hints_cons _ _ _ (der_15084 v h) (hints_cons _ _ _ (der_15085 v h) (hints_cons _ _ _ (der_15086 v h) (hints_cons _ _ _ (der_15087 v h) (hints_cons _ _ _ (der_15088 v h) (hints_cons _ _ _ (der_15089 v h) (hints_cons _ _ _ (der_15090 v h) (hints_cons _ _ _ (der_15091 v h) (hints_cons _ _ _ (der_15092 v h) (hints_cons _ _ _ (der_15093 v h) (hints_cons _ _ _ (der_15094 v h) (hints_cons _ _ _ (der_15095 v h) (hints_cons _ _ _ (der_15096 v h) (hints_cons _ _ _ (der_15097 v h) (hints_cons _ _ _ (der_15098 v h) (hints_cons _ _ _ (der_15099 v h) (hints_cons _ _ _ (der_15100 v h) (hints_cons _ _ _ (der_15101 v h) (hints_cons _ _ _ (der_15102 v h) (hints_cons _ _ _ (der_15103 v h) (hints_cons _ _ _ (der_15104 v h) (hints_cons _ _ _ (der_15105 v h) (hints_cons _ _ _ (der_15106 v h) (hints_cons _ _ _ (der_15107 v h) (hints_cons _ _ _ (der_15108 v h) (hints_cons _ _ _ (der_15109 v h) (hints_cons _ _ _ (der_15110 v h) (hints_cons _ _ _ (der_15111 v h) (hints_cons _ _ _ (der_15112 v h) (hints_cons _ _ _ (der_15113 v h) (hints_cons _ _ _ (der_15114 v h) (hints_cons _ _ _ (der_15115 v h) (hints_cons _ _ _ (der_15116 v h) (hints_cons _ _ _ (der_15117 v h) (hints_cons _ _ _ (der_15118 v h) (hints_cons _ _ _ (der_15119 v h) (hints_cons _ _ _ (der_15120 v h) (hints_cons _ _ _ (der_15121 v h) (hints_cons _ _ _ (der_15122 v h) (hints_cons _ _ _ (der_15123 v h) (hints_cons _ _ _ (der_15124 v h) (hints_cons _ _ _ (der_15125 v h) (hints_cons _ _ _ (der_15126 v h) (hints_cons _ _ _ (der_15127 v h) (hints_cons _ _ _ (der_15128 v h) (hints_cons _ _ _ (der_15129 v h) (hints_cons _ _ _ (der_15130 v h) (hints_cons _ _ _ (der_15131 v h) (hints_cons _ _ _ (der_15132 v h) (hints_cons _ _ _ (der_15133 v h) (hints_cons _ _ _ (der_15134 v h) (hints_cons _ _ _ (der_15135 v h) (hints_cons _ _ _ (der_15136 v h) (hints_cons _ _ _ (der_15137 v h) (hints_cons _ _ _ (der_15138 v h) (hints_cons _ _ _ (der_15139 v h) (hints_cons _ _ _ (der_15140 v h) (hints_cons _ _ _ (der_15141 v h) (hints_cons _ _ _ (der_15142 v h) (hints_cons _ _ _ (der_15143 v h) (hints_cons _ _ _ (der_15144 v h) (hints_cons _ _ _ (der_15145 v h) (hints_cons _ _ _ (der_15146 v h) (hints_cons _ _ _ (der_15147 v h) (hints_cons _ _ _ (der_15148 v h) (hints_cons _ _ _ (der_15149 v h) (hints_cons _ _ _ (der_15150 v h) (hints_cons _ _ _ (der_15151 v h) (hints_cons _ _ _ (der_15152 v h) (hints_cons _ _ _ (der_15153 v h) (hints_cons _ _ _ (der_15154 v h) (hints_cons _ _ _ (der_15155 v h) (hints_cons _ _ _ (der_15156 v h) (hints_cons _ _ _ (der_15157 v h) (hints_cons _ _ _ (der_15158 v h) (hints_cons _ _ _ (der_15159 v h) (hints_cons _ _ _ (der_15160 v h) (hints_cons _ _ _ (der_15161 v h) (hints_cons _ _ _ (der_15162 v h) (hints_cons _ _ _ (der_15163 v h) (hints_cons _ _ _ (der_15164 v h) (hints_cons _ _ _ (der_15165 v h) (hints_cons _ _ _ (der_15166 v h) (hints_cons _ _ _ (der_15167 v h) (hints_cons _ _ _ (der_15168 v h) (hints_cons _ _ _ (der_15169 v h) (hints_cons _ _ _ (der_15170 v h) (hints_cons _ _ _ (der_15171 v h) (hints_cons _ _ _ (der_15172 v h) (hints_cons _ _ _ (der_15173 v h) (hints_cons _ _ _ (der_15175 v h) (hints_cons _ _ _ (der_15176 v h) (hints_cons _ _ _ (der_15177 v h) (hints_cons _ _ _ (der_15178 v h) (hints_cons _ _ _ (der_15179 v h) (hints_cons _ _ _ (der_15180 v h) (hints_cons _ _ _ (der_15181 v h) (hints_cons _ _ _ (der_15182 v h) (hints_cons _ _ _ (der_15183 v h) (hints_cons _ _ _ (der_15184 v h) (hints_cons _ _ _ (der_15185 v h) (hints_cons _ _ _ (der_15186 v h) (hints_cons _ _ _ (der_15187 v h) (hints_cons _ _ _ (der_15188 v h) (hints_cons _ _ _ (der_15189 v h) (hints_cons _ _ _ (der_15190 v h) (hints_cons _ _ _ (der_15191 v h) (hints_cons _ _ _ (der_15192 v h) (hints_cons _ _ _ (der_15193 v h) (hints_cons _ _ _ (der_15194 v h) (hints_cons _ _ _ (der_15195 v h) (hints_cons _ _ _ (der_15196 v h) (hints_cons _ _ _ (der_15197 v h) (hints_cons _ _ _ (der_15198 v h) (hints_cons _ _ _ (der_15199 v h) (hints_cons _ _ _ (der_15200 v h) (hints_cons _ _ _ (der_15201 v h) (hints_cons _ _ _ (der_15202 v h) (hints_cons _ _ _ (der_15203 v h) (hints_cons _ _ _ (der_15204 v h) (hints_cons _ _ _ (der_15205 v h) (hints_cons _ _ _ (der_15206 v h) (hints_cons _ _ _ (der_15207 v h) (hints_cons _ _ _ (der_15208 v h) (hints_cons _ _ _ (der_15209 v h) (hints_cons _ _ _ (der_15210 v h) (hints_cons _ _ _ (der_15211 v h) (hints_cons _ _ _ (der_15212 v h) (hints_cons _ _ _ (der_15213 v h) (hints_cons _ _ _ (der_15214 v h) (hints_cons _ _ _ (der_15215 v h) (hints_cons _ _ _ (der_15216 v h) (hints_cons _ _ _ (der_15217 v h) (hints_cons _ _ _ (der_15218 v h) (hints_cons _ _ _ (der_15219 v h) (hints_cons _ _ _ (der_15220 v h) (hints_cons _ _ _ (der_15221 v h) (hints_cons _ _ _ (der_15222 v h) (hints_cons _ _ _ (der_15223 v h) (hints_cons _ _ _ (der_15224 v h) (hints_cons _ _ _ (der_15225 v h) (hints_cons _ _ _ (der_15226 v h) (hints_cons _ _ _ (der_15227 v h) (hints_cons _ _ _ (der_15228 v h) (hints_cons _ _ _ (der_15229 v h) (hints_cons _ _ _ (der_15230 v h) (hints_cons _ _ _ (der_15231 v h) (hints_cons _ _ _ (der_15232 v h) (hints_cons _ _ _ (der_15233 v h) (hints_cons _ _ _ (der_15234 v h) (hints_cons _ _ _ (der_15235 v h) (hints_cons _ _ _ (der_15236 v h) (hints_cons _ _ _ (der_15237 v h) (hints_cons _ _ _ (der_15238 v h) (hints_cons _ _ _ (der_15239 v h) (hints_cons _ _ _ (der_15240 v h) (hints_cons _ _ _ (der_15241 v h) (hints_cons _ _ _ (der_15242 v h) (hints_cons _ _ _ (der_15243 v h) (hints_cons _ _ _ (der_15244 v h) (hints_cons _ _ _ (der_15245 v h) (hints_cons _ _ _ (der_15246 v h) (hints_cons _ _ _ (der_15247 v h) (hints_cons _ _ _ (der_15248 v h) (hints_cons _ _ _ (der_15249 v h) (hints_cons _ _ _ (der_15250 v h) (hints_cons _ _ _ (der_15251 v h) (hints_cons _ _ _ (der_15252 v h) (hints_cons _ _ _ (der_15253 v h) (hints_cons _ _ _ (der_15254 v h) (hints_cons _ _ _ (der_15255 v h) (hints_cons _ _ _ (der_15256 v h) (hints_cons _ _ _ (der_15257 v h) (hints_cons _ _ _ (der_15258 v h) (hints_cons _ _ _ (der_15259 v h) (hints_cons _ _ _ (der_15260 v h) (hints_cons _ _ _ (der_15261 v h) (hints_cons _ _ _ (der_15262 v h) (hints_cons _ _ _ (der_15263 v h) (hints_cons _ _ _ (der_15264 v h) (hints_cons _ _ _ (der_15265 v h) (hints_cons _ _ _ (der_15267 v h) (hints_cons _ _ _ (der_15268 v h) (hints_cons _ _ _ (der_15269 v h) (hints_cons _ _ _ (der_15270 v h) (hints_cons _ _ _ (der_15271 v h) (hints_cons _ _ _ (der_15272 v h) (hints_cons _ _ _ (der_15273 v h) (hints_cons _ _ _ (der_15274 v h) (hints_cons _ _ _ (der_15275 v h) (hints_cons _ _ _ (der_15276 v h) (hints_cons _ _ _ (der_15277 v h) (hints_cons _ _ _ (der_15278 v h) (hints_cons _ _ _ (der_15279 v h) (hints_cons _ _ _ (der_15280 v h) (hints_cons _ _ _ (der_15281 v h) (hints_cons _ _ _ (der_15283 v h) (hints_cons _ _ _ (der_15284 v h) (hints_cons _ _ _ (der_15285 v h) (hints_cons _ _ _ (der_15286 v h) (hints_cons _ _ _ (der_15287 v h) (hints_cons _ _ _ (der_15288 v h) (hints_cons _ _ _ (der_15289 v h) (hints_cons _ _ _ (der_15290 v h) (hints_cons _ _ _ (der_15291 v h) (hints_cons _ _ _ (der_15292 v h) (hints_cons _ _ _ (der_15293 v h) (hints_cons _ _ _ (der_15294 v h) (hints_cons _ _ _ (der_15295 v h) (hints_cons _ _ _ (der_15296 v h) (hints_cons _ _ _ (der_15297 v h) (hints_cons _ _ _ (der_15298 v h) (hints_cons _ _ _ (der_15299 v h) (hints_cons _ _ _ (der_15300 v h) (hints_cons _ _ _ (der_15301 v h) (hints_cons _ _ _ (der_15302 v h) (hints_cons _ _ _ (der_15303 v h) (hints_cons _ _ _ (der_15304 v h) (hints_cons _ _ _ (der_15305 v h) (hints_cons _ _ _ (der_15306 v h) (hints_cons _ _ _ (der_15307 v h) (hints_cons _ _ _ (der_15308 v h) (hints_cons _ _ _ (der_15309 v h) (hints_cons _ _ _ (der_15310 v h) (hints_cons _ _ _ (der_15311 v h) (hints_cons _ _ _ (der_15312 v h) (hints_cons _ _ _ (der_15313 v h) (hints_cons _ _ _ (der_15315 v h) (hints_cons _ _ _ (der_15316 v h) (hints_cons _ _ _ (der_15317 v h) (hints_cons _ _ _ (der_15318 v h) (hints_cons _ _ _ (der_15319 v h) (hints_cons _ _ _ (der_15320 v h) (hints_cons _ _ _ (der_15321 v h) (hints_cons _ _ _ (der_15322 v h) (hints_cons _ _ _ (der_15323 v h) (hints_cons _ _ _ (der_15324 v h) (hints_cons _ _ _ (der_15325 v h) (hints_cons _ _ _ (der_15326 v h) (hints_cons _ _ _ (der_15327 v h) (hints_cons _ _ _ (der_15328 v h) (hints_cons _ _ _ (der_15329 v h) (hints_cons _ _ _ (der_15330 v h) (hints_cons _ _ _ (der_15331 v h) (hints_cons _ _ _ (der_15332 v h) (hints_cons _ _ _ (der_15333 v h) (hints_cons _ _ _ (der_15334 v h) (hints_cons _ _ _ (der_15335 v h) (hints_cons _ _ _ (der_15336 v h) (hints_cons _ _ _ (der_15337 v h) (hints_cons _ _ _ (der_15338 v h) (hints_cons _ _ _ (der_15339 v h) (hints_cons _ _ _ (der_15340 v h) (hints_cons _ _ _ (der_15341 v h) (hints_cons _ _ _ (der_15342 v h) (hints_cons _ _ _ (der_15343 v h) (hints_cons _ _ _ (der_15345 v h) (hints_cons _ _ _ (der_15346 v h) (hints_cons _ _ _ (der_15347 v h) (hints_cons _ _ _ (der_15348 v h) (hints_cons _ _ _ (der_15349 v h) (hints_cons _ _ _ (der_15350 v h) (hints_cons _ _ _ (der_15351 v h) (hints_cons _ _ _ (der_15352 v h) (hints_cons _ _ _ (der_15353 v h) (hints_cons _ _ _ (der_15354 v h) (hints_cons _ _ _ (der_15355 v h) (hints_cons _ _ _ (der_15356 v h) (hints_cons _ _ _ (der_15357 v h) (hints_cons _ _ _ (der_15358 v h) (hints_cons _ _ _ (der_15359 v h) (hints_cons _ _ _ (der_15360 v h) (hints_cons _ _ _ (der_15361 v h) (hints_cons _ _ _ (der_15362 v h) (hints_cons _ _ _ (der_15363 v h) (hints_cons _ _ _ (der_15364 v h) (hints_cons _ _ _ (der_15365 v h) (hints_cons _ _ _ (der_15366 v h) (hints_cons _ _ _ (der_15367 v h) (hints_cons _ _ _ (der_15368 v h) (hints_cons _ _ _ (der_15369 v h) (hints_cons _ _ _ (der_15370 v h) (hints_cons _ _ _ (der_15371 v h) (hints_cons _ _ _ (der_15372 v h) (hints_cons _ _ _ (der_15373 v h) (hints_cons _ _ _ (der_15374 v h) (hints_cons _ _ _ (der_15375 v h) (hints_cons _ _ _ (der_15377 v h) (hints_cons _ _ _ (der_15378 v h) (hints_cons _ _ _ (der_15379 v h) (hints_cons _ _ _ (der_15380 v h) (hints_cons _ _ _ (der_15381 v h) (hints_cons _ _ _ (der_15382 v h) (hints_cons _ _ _ (der_15383 v h) (hints_cons _ _ _ (der_15384 v h) (hints_cons _ _ _ (der_15385 v h) (hints_cons _ _ _ (der_15386 v h) (hints_cons _ _ _ (der_15387 v h) (hints_cons _ _ _ (der_15388 v h) (hints_cons _ _ _ (der_15389 v h) (hints_cons _ _ _ (der_15390 v h) (hints_cons _ _ _ (der_15391 v h) (hints_cons _ _ _ (der_15392 v h) (hints_cons _ _ _ (der_15393 v h) (hints_cons _ _ _ (der_15394 v h) (hints_cons _ _ _ (der_15395 v h) (hints_cons _ _ _ (der_15396 v h) (hints_cons _ _ _ (der_15397 v h) (hints_cons _ _ _ (der_15398 v h) (hints_cons _ _ _ (der_15399 v h) (hints_cons _ _ _ (der_15400 v h) (hints_cons _ _ _ (der_15401 v h) (hints_cons _ _ _ (der_15402 v h) (hints_cons _ _ _ (der_15403 v h) (hints_cons _ _ _ (der_15404 v h) (hints_cons _ _ _ (der_15405 v h) (hints_cons _ _ _ (der_15406 v h) (hints_cons _ _ _ (der_15407 v h) (hints_cons _ _ _ (der_15408 v h) (hints_cons _ _ _ (der_15409 v h) (hints_cons _ _ _ (der_15410 v h) (hints_cons _ _ _ (der_15411 v h) (hints_cons _ _ _ (der_15412 v h) (hints_cons _ _ _ (der_15413 v h) (hints_cons _ _ _ (der_15414 v h) (hints_cons _ _ _ (der_15415 v h) (hints_cons _ _ _ (der_15416 v h) (hints_cons _ _ _ (der_15417 v h) (hints_cons _ _ _ (der_15418 v h) (hints_cons _ _ _ (der_15419 v h) (hints_cons _ _ _ (der_15420 v h) (hints_cons _ _ _ (der_15421 v h) (hints_cons _ _ _ (der_15422 v h) (hints_cons _ _ _ (der_15423 v h) (hints_cons _ _ _ (der_15425 v h) (hints_cons _ _ _ (der_15426 v h) (hints_cons _ _ _ (der_15427 v h) (hints_cons _ _ _ (der_15428 v h) (hints_cons _ _ _ (der_15429 v h) (hints_cons _ _ _ (der_15430 v h) (hints_cons _ _ _ (der_15431 v h) (hints_cons _ _ _ (der_15432 v h) (hints_cons _ _ _ (der_15433 v h) (hints_cons _ _ _ (der_15434 v h) (hints_cons _ _ _ (der_15435 v h) (hints_cons _ _ _ (der_15436 v h) (hints_cons _ _ _ (der_15437 v h) (hints_cons _ _ _ (der_15438 v h) (hints_cons _ _ _ (der_15439 v h) (hints_cons _ _ _ (der_15440 v h) (hints_cons _ _ _ (der_15441 v h) (hints_cons _ _ _ (der_15442 v h) (hints_cons _ _ _ (der_15443 v h) (hints_cons _ _ _ (der_15444 v h) (hints_cons _ _ _ (der_15445 v h) (hints_cons _ _ _ (der_15446 v h) (hints_cons _ _ _ (der_15447 v h) (hints_cons _ _ _ (der_15448 v h) (hints_cons _ _ _ (der_15449 v h) (hints_cons _ _ _ (der_15450 v h) (hints_cons _ _ _ (der_15451 v h) (hints_cons _ _ _ (der_15452 v h) (hints_cons _ _ _ (der_15453 v h) (hints_cons _ _ _ (der_15454 v h) (hints_cons _ _ _ (der_15455 v h) (hints_cons _ _ _ (der_15456 v h) (hints_cons _ _ _ (der_15457 v h) (hints_cons _ _ _ (der_15458 v h) (hints_cons _ _ _ (der_15459 v h) (hints_cons _ _ _ (der_15460 v h) (hints_cons _ _ _ (der_15461 v h) (hints_cons _ _ _ (der_15462 v h) (hints_cons _ _ _ (der_15463 v h) (hints_cons _ _ _ (der_15464 v h) (hints_cons _ _ _ (der_15465 v h) (hints_cons _ _ _ (der_15466 v h) (hints_cons _ _ _ (der_15467 v h) (hints_cons _ _ _ (der_15468 v h) (hints_cons _ _ _ (der_15469 v h) (hints_cons _ _ _ (der_15470 v h) (hints_cons _ _ _ (der_15471 v h) (hints_cons _ _ _ (der_15472 v h) (hints_cons _ _ _ (der_15473 v h) (hints_cons _ _ _ (der_15474 v h) (hints_cons _ _ _ (der_15475 v h) (hints_cons _ _ _ (der_15476 v h) (hints_cons _ _ _ (der_15477 v h) (hints_cons _ _ _ (der_15478 v h) (hints_cons _ _ _ (der_15479 v h) (hints_cons _ _ _ (der_15480 v h) (hints_cons _ _ _ (der_15481 v h) (hints_cons _ _ _ (der_15482 v h) (hints_cons _ _ _ (der_15483 v h) (hints_cons _ _ _ (der_15484 v h) (hints_cons _ _ _ (der_15485 v h) (hints_cons _ _ _ (der_15486 v h) (hints_cons _ _ _ (der_15487 v h) (hints_cons _ _ _ (der_15488 v h) (hints_cons _ _ _ (der_15489 v h) (hints_cons _ _ _ (der_15490 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix000 := chunk000
theorem prefix_sound000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix000, CNF.Holds (v ∘ decodeVar) c := chunk_sound000 v h
end Percolation.NReplay
