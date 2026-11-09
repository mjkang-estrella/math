import NReplay048
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_52038 : CNF.NClause := [(87,false),(65,false),(34,false),(75,false),(80,true)]
theorem der_52038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52038 :=
  CNF.rup_sound cl_52038 [cl_37953,cl_33090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37953 v h) (hints_cons _ _ _ (der_33090 v h) (by intro d hd; cases hd)))
def cl_52039 : CNF.NClause := [(80,true),(81,false),(79,false),(78,false),(46,false)]
theorem der_52039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52039 :=
  CNF.rup_sound cl_52039 [cl_35872,cl_32943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35872 v h) (hints_cons _ _ _ (der_32943 v h) (by intro d hd; cases hd)))
def cl_52040 : CNF.NClause := [(73,false),(38,false),(64,true),(80,true),(82,false)]
theorem der_52040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52040 :=
  CNF.rup_sound cl_52040 [cl_37955,cl_51143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37955 v h) (hints_cons _ _ _ (der_51143 v h) (by intro d hd; cases hd)))
def cl_52041 : CNF.NClause := [(80,true),(38,false),(89,false),(64,false),(82,false)]
theorem der_52041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52041 :=
  CNF.rup_sound cl_52041 [cl_36966,cl_51147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36966 v h) (hints_cons _ _ _ (der_51147 v h) (by intro d hd; cases hd)))
def cl_52042 : CNF.NClause := [(68,false),(64,false),(81,false),(43,false),(72,true)]
theorem der_52042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52042 :=
  CNF.rup_sound cl_52042 [cl_36397,cl_33316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36397 v h) (hints_cons _ _ _ (der_33316 v h) (by intro d hd; cases hd)))
def cl_52043 : CNF.NClause := [(3,true),(87,false),(34,false),(75,false),(70,false)]
theorem der_52043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52043 :=
  CNF.rup_sound cl_52043 [cl_39162,cl_50968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39162 v h) (hints_cons _ _ _ (der_50968 v h) (by intro d hd; cases hd)))
def cl_52044 : CNF.NClause := [(89,false),(38,false),(64,true),(73,false),(82,false)]
theorem der_52044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52044 :=
  CNF.rup_sound cl_52044 [cl_39180,cl_33437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39180 v h) (hints_cons _ _ _ (der_33437 v h) (by intro d hd; cases hd)))
def cl_52045 : CNF.NClause := [(70,true),(81,false),(59,false),(90,false),(84,false)]
theorem der_52045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52045 :=
  CNF.rup_sound cl_52045 [cl_39573,cl_51180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39573 v h) (hints_cons _ _ _ (der_51180 v h) (by intro d hd; cases hd)))
def cl_52046 : CNF.NClause := [(102,true),(57,true),(32,false),(51,false),(38,true)]
theorem der_52046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52046 :=
  CNF.rup_sound cl_52046 [cl_39709,cl_51503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39709 v h) (hints_cons _ _ _ (der_51503 v h) (by intro d hd; cases hd)))
def cl_52047 : CNF.NClause := [(15,true),(81,true),(1,false),(125,false),(136,true)]
theorem der_52047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52047 :=
  CNF.rup_sound cl_52047 [cl_39471,cl_49792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39471 v h) (hints_cons _ _ _ (der_49792 v h) (by intro d hd; cases hd)))
def cl_52048 : CNF.NClause := [(36,false),(43,true),(116,true),(34,false),(52,true)]
theorem der_52048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52048 :=
  CNF.rup_sound cl_52048 [cl_38274,cl_49848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38274 v h) (hints_cons _ _ _ (der_49848 v h) (by intro d hd; cases hd)))
def cl_52049 : CNF.NClause := [(70,true),(6,true),(14,false),(17,true),(138,false)]
theorem der_52049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52049 :=
  CNF.rup_sound cl_52049 [cl_38451,cl_49773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38451 v h) (hints_cons _ _ _ (der_49773 v h) (by intro d hd; cases hd)))
def cl_52050 : CNF.NClause := [(59,false),(33,true),(47,false),(115,true),(55,true)]
theorem der_52050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52050 :=
  CNF.rup_sound cl_52050 [cl_43536,cl_49911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43536 v h) (hints_cons _ _ _ (der_49911 v h) (by intro d hd; cases hd)))
def cl_52051 : CNF.NClause := [(3,true),(6,true),(17,false),(28,false),(70,true)]
theorem der_52051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52051 :=
  CNF.rup_sound cl_52051 [cl_41772,cl_50163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41772 v h) (hints_cons _ _ _ (der_50163 v h) (by intro d hd; cases hd)))
def cl_52052 : CNF.NClause := [(63,false),(45,false),(89,false),(70,false),(14,true)]
theorem der_52052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52052 :=
  CNF.rup_sound cl_52052 [cl_42561,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42561 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_52053 : CNF.NClause := [(345,false),(4,false),(68,true),(8,true),(7,true)]
theorem der_52053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52053 :=
  CNF.rup_sound cl_52053 [cl_41822,cl_49989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41822 v h) (hints_cons _ _ _ (der_49989 v h) (by intro d hd; cases hd)))
def cl_52054 : CNF.NClause := [(76,false),(63,true),(55,false),(80,false),(67,false)]
theorem der_52054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52054 :=
  CNF.rup_sound cl_52054 [cl_42847,cl_50889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42847 v h) (hints_cons _ _ _ (der_50889 v h) (by intro d hd; cases hd)))
def cl_52055 : CNF.NClause := [(79,false),(21,true),(52,false),(85,false),(67,false)]
theorem der_52055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52055 :=
  CNF.rup_sound cl_52055 [cl_43749,cl_51768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43749 v h) (hints_cons _ _ _ (der_51768 v h) (by intro d hd; cases hd)))
def cl_52056 : CNF.NClause := [(45,false),(79,false),(11,false),(72,true),(89,false)]
theorem der_52056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52056 :=
  CNF.rup_sound cl_52056 [cl_42698,cl_51886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42698 v h) (hints_cons _ _ _ (der_51886 v h) (by intro d hd; cases hd)))
def cl_52057 : CNF.NClause := [(50,true),(58,false),(116,true),(43,true),(34,false)]
theorem der_52057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52057 :=
  CNF.rup_sound cl_52057 [cl_42685,cl_45242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42685 v h) (hints_cons _ _ _ (der_45242 v h) (by intro d hd; cases hd)))
def cl_52058 : CNF.NClause := [(69,false),(40,false),(81,false),(75,false),(9,true)]
theorem der_52058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52058 :=
  CNF.rup_sound cl_52058 [cl_41697,cl_47453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41697 v h) (hints_cons _ _ _ (der_47453 v h) (by intro d hd; cases hd)))
def cl_52059 : CNF.NClause := [(70,true),(6,true),(17,false),(14,true),(141,false)]
theorem der_52059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52059 :=
  CNF.rup_sound cl_52059 [cl_42001,cl_50100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42001 v h) (hints_cons _ _ _ (der_50100 v h) (by intro d hd; cases hd)))
def cl_52061 : CNF.NClause := [(92,false),(36,false),(84,true),(85,false),(5,true)]
theorem der_52061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52061 :=
  CNF.rup_sound cl_52061 [cl_43057,cl_32304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43057 v h) (hints_cons _ _ _ (der_32304 v h) (by intro d hd; cases hd)))
def cl_52063 : CNF.NClause := [(75,false),(83,false),(57,false),(26,true),(79,true)]
theorem der_52063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52063 :=
  CNF.rup_sound cl_52063 [cl_42675,cl_51347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42675 v h) (hints_cons _ _ _ (der_51347 v h) (by intro d hd; cases hd)))
def cl_52064 : CNF.NClause := [(40,false),(63,false),(75,false),(69,false),(9,true)]
theorem der_52064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52064 :=
  CNF.rup_sound cl_52064 [cl_41638,cl_50732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41638 v h) (hints_cons _ _ _ (der_50732 v h) (by intro d hd; cases hd)))
def cl_52065 : CNF.NClause := [(40,false),(81,false),(75,false),(69,false),(9,true)]
theorem der_52065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52065 :=
  CNF.rup_sound cl_52065 [cl_42950,cl_50851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42950 v h) (hints_cons _ _ _ (der_50851 v h) (by intro d hd; cases hd)))
def cl_52066 : CNF.NClause := [(73,false),(52,false),(21,true),(85,false),(67,false)]
theorem der_52066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52066 :=
  CNF.rup_sound cl_52066 [cl_42784,cl_51579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42784 v h) (hints_cons _ _ _ (der_51579 v h) (by intro d hd; cases hd)))
def cl_52067 : CNF.NClause := [(68,false),(82,true),(76,false),(79,false),(39,false)]
theorem der_52067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52067 :=
  CNF.rup_sound cl_52067 [cl_44992,cl_50615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44992 v h) (hints_cons _ _ _ (der_50615 v h) (by intro d hd; cases hd)))
def cl_52068 : CNF.NClause := [(74,false),(33,false),(79,false),(2,true),(69,false)]
theorem der_52068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52068 :=
  CNF.rup_sound cl_52068 [cl_44263,cl_49699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44263 v h) (hints_cons _ _ _ (der_49699 v h) (by intro d hd; cases hd)))
def cl_52069 : CNF.NClause := [(45,false),(79,false),(89,false),(70,false),(14,true)]
theorem der_52069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52069 :=
  CNF.rup_sound cl_52069 [cl_45019,cl_51828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45019 v h) (hints_cons _ _ _ (der_51828 v h) (by intro d hd; cases hd)))
def cl_52070 : CNF.NClause := [(89,false),(45,false),(79,false),(14,true),(70,false)]
theorem der_52070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52070 :=
  CNF.rup_sound cl_52070 [cl_46688,cl_50734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46688 v h) (hints_cons _ _ _ (der_50734 v h) (by intro d hd; cases hd)))
def cl_52073 : CNF.NClause := [(80,false),(76,false),(55,false),(67,false),(24,true)]
theorem der_52073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52073 :=
  CNF.rup_sound cl_52073 [cl_44104,cl_52054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44104 v h) (hints_cons _ _ _ (der_52054 v h) (by intro d hd; cases hd)))
def cl_52077 : CNF.NClause := [(37,false),(82,true),(74,false),(70,false),(78,false)]
theorem der_52077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52077 :=
  CNF.rup_sound cl_52077 [cl_45568,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45568 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def cl_52078 : CNF.NClause := [(32,false),(76,false),(1,true),(81,false),(87,false)]
theorem der_52078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52078 :=
  CNF.rup_sound cl_52078 [cl_47618,cl_43007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47618 v h) (hints_cons _ _ _ (der_43007 v h) (by intro d hd; cases hd)))
def cl_52081 : CNF.NClause := [(88,false),(52,false),(85,false),(67,false),(79,true)]
theorem der_52081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52081 :=
  CNF.rup_sound cl_52081 [cl_47971,cl_34573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47971 v h) (hints_cons _ _ _ (der_34573 v h) (by intro d hd; cases hd)))
def cl_52083 : CNF.NClause := [(3,true),(10,false),(75,true),(150,true),(134,false)]
theorem der_52083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52083 :=
  CNF.rup_sound cl_52083 [cl_48715,cl_49811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48715 v h) (hints_cons _ _ _ (der_49811 v h) (by intro d hd; cases hd)))
def cl_52084 : CNF.NClause := [(3,true),(85,true),(21,false),(151,true),(145,false)]
theorem der_52084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52084 :=
  CNF.rup_sound cl_52084 [cl_48792,cl_50532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48792 v h) (hints_cons _ _ _ (der_50532 v h) (by intro d hd; cases hd)))
def cl_52085 : CNF.NClause := [(81,true),(9,true),(12,false),(15,true),(136,false)]
theorem der_52085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52085 :=
  CNF.rup_sound cl_52085 [cl_48806,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48806 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_52087 : CNF.NClause := [(3,true),(9,true),(75,true),(909,true),(921,false)]
theorem der_52087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52087 :=
  CNF.rup_sound cl_52087 [cl_49016,cl_15888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49016 v h) (hints_cons _ _ _ (der_15888 v h) (by intro d hd; cases hd)))
def cl_52088 : CNF.NClause := [(3,true),(6,true),(24,false),(91,true),(241,false)]
theorem der_52088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52088 :=
  CNF.rup_sound cl_52088 [cl_49074,cl_49776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49074 v h) (hints_cons _ _ _ (der_49776 v h) (by intro d hd; cases hd)))
def cl_52089 : CNF.NClause := [(76,false),(58,false),(69,true),(85,false),(78,false)]
theorem der_52089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52089 :=
  CNF.rup_sound cl_52089 [cl_49169,cl_32487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49169 v h) (hints_cons _ _ _ (der_32487 v h) (by intro d hd; cases hd)))
def cl_52090 : CNF.NClause := [(40,false),(81,false),(69,true),(75,false),(88,false)]
theorem der_52090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52090 :=
  CNF.rup_sound cl_52090 [cl_49188,cl_32656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49188 v h) (hints_cons _ _ _ (der_32656 v h) (by intro d hd; cases hd)))
def cl_52091 : CNF.NClause := [(67,false),(81,false),(54,false),(74,false),(83,true)]
theorem der_52091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52091 :=
  CNF.rup_sound cl_52091 [cl_49219,cl_50800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49219 v h) (hints_cons _ _ _ (der_50800 v h) (by intro d hd; cases hd)))
def cl_52092 : CNF.NClause := [(40,false),(9,true),(81,false),(75,false),(88,false)]
theorem der_52092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52092 :=
  CNF.rup_sound cl_52092 [cl_49251,cl_52058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49251 v h) (hints_cons _ _ _ (der_52058 v h) (by intro d hd; cases hd)))
def cl_52093 : CNF.NClause := [(42,false),(72,false),(69,true),(66,false),(90,false)]
theorem der_52093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52093 :=
  CNF.rup_sound cl_52093 [cl_49277,cl_33009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49277 v h) (hints_cons _ _ _ (der_33009 v h) (by intro d hd; cases hd)))
def cl_52094 : CNF.NClause := [(72,false),(85,true),(43,false),(81,false),(68,false)]
theorem der_52094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52094 :=
  CNF.rup_sound cl_52094 [cl_49278,cl_51067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49278 v h) (hints_cons _ _ _ (der_51067 v h) (by intro d hd; cases hd)))
def cl_52095 : CNF.NClause := [(65,false),(68,true),(39,false),(79,false),(90,false)]
theorem der_52095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52095 :=
  CNF.rup_sound cl_52095 [cl_49316,cl_42425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49316 v h) (hints_cons _ _ _ (der_42425 v h) (by intro d hd; cases hd)))
def cl_52097 : CNF.NClause := [(45,false),(63,true),(89,false),(72,false),(86,false)]
theorem der_52097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52097 :=
  CNF.rup_sound cl_52097 [cl_49519,cl_51883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49519 v h) (hints_cons _ _ _ (der_51883 v h) (by intro d hd; cases hd)))
def cl_52099 : CNF.NClause := [(86,false),(14,true),(1,true),(18,true),(5,true),(29,true)]
theorem der_52099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52099 :=
  CNF.rup_sound cl_52099 [cl_1584,cl_48506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1584 v h) (hints_cons _ _ _ (der_48506 v h) (by intro d hd; cases hd)))
def cl_52100 : CNF.NClause := [(22,true),(86,false),(1,true),(14,true),(5,true),(29,true)]
theorem der_52100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52100 :=
  CNF.rup_sound cl_52100 [cl_1592,cl_48506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1592 v h) (hints_cons _ _ _ (der_48506 v h) (by intro d hd; cases hd)))
def cl_52101 : CNF.NClause := [(22,true),(86,false),(29,true),(1,true),(5,true),(18,true)]
theorem der_52101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52101 :=
  CNF.rup_sound cl_52101 [cl_1596,cl_52100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1596 v h) (hints_cons _ _ _ (der_52100 v h) (by intro d hd; cases hd)))
def cl_52102 : CNF.NClause := [(86,false),(1,true),(29,true),(22,true),(14,true),(18,true)]
theorem der_52102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52102 :=
  CNF.rup_sound cl_52102 [cl_1598,cl_52100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1598 v h) (hints_cons _ _ _ (der_52100 v h) (by intro d hd; cases hd)))
def cl_52103 : CNF.NClause := [(22,true),(86,false),(14,true),(18,true),(5,true),(29,true)]
theorem der_52103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52103 :=
  CNF.rup_sound cl_52103 [cl_1599,cl_48506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1599 v h) (hints_cons _ _ _ (der_48506 v h) (by intro d hd; cases hd)))
def cl_52104 : CNF.NClause := [(32,false),(76,false),(71,false),(86,false),(1,false),(87,true)]
theorem der_52104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52104 :=
  CNF.rup_sound cl_52104 [cl_34876,cl_34119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34876 v h) (hints_cons _ _ _ (der_34119 v h) (by intro d hd; cases hd)))
def cl_52105 : CNF.NClause := [(69,false),(73,false),(65,false),(18,true),(49,false),(86,false)]
theorem der_52105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52105 :=
  CNF.rup_sound cl_52105 [cl_26318,cl_49717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26318 v h) (hints_cons _ _ _ (der_49717 v h) (by intro d hd; cases hd)))
def cl_52107 : CNF.NClause := [(50,false),(90,false),(63,false),(19,true),(85,false),(71,false)]
theorem der_52107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52107 :=
  CNF.rup_sound cl_52107 [cl_26320,cl_50714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26320 v h) (hints_cons _ _ _ (der_50714 v h) (by intro d hd; cases hd)))
def cl_52109 : CNF.NClause := [(73,false),(4,true),(35,false),(83,false),(68,false),(63,true)]
theorem der_52109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52109 :=
  CNF.rup_sound cl_52109 [cl_26324,cl_51306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26324 v h) (hints_cons _ _ _ (der_51306 v h) (by intro d hd; cases hd)))
def cl_52110 : CNF.NClause := [(79,false),(46,false),(78,false),(15,false),(92,false),(77,true)]
theorem der_52110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52110 :=
  CNF.rup_sound cl_52110 [cl_26326,cl_32913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26326 v h) (hints_cons _ _ _ (der_32913 v h) (by intro d hd; cases hd)))
def cl_52111 : CNF.NClause := [(17,true),(70,false),(3,true),(6,true),(14,true),(28,true)]
theorem der_52111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52111 :=
  CNF.rup_sound cl_52111 [cl_560,cl_37568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_560 v h) (hints_cons _ _ _ (der_37568 v h) (by intro d hd; cases hd)))
def cl_52112 : CNF.NClause := [(3,true),(70,false),(28,true),(20,true),(14,true),(6,true)]
theorem der_52112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52112 :=
  CNF.rup_sound cl_52112 [cl_568,cl_37568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_568 v h) (hints_cons _ _ _ (der_37568 v h) (by intro d hd; cases hd)))
def cl_52113 : CNF.NClause := [(17,true),(28,true),(70,false),(20,true),(6,true),(3,true)]
theorem der_52113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52113 :=
  CNF.rup_sound cl_52113 [cl_572,cl_37568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_572 v h) (hints_cons _ _ _ (der_37568 v h) (by intro d hd; cases hd)))
def cl_52114 : CNF.NClause := [(17,true),(20,true),(3,true),(28,true),(70,false),(14,true)]
theorem der_52114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52114 :=
  CNF.rup_sound cl_52114 [cl_574,cl_37568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_574 v h) (hints_cons _ _ _ (der_37568 v h) (by intro d hd; cases hd)))
def cl_52115 : CNF.NClause := [(17,true),(20,true),(28,true),(70,false),(6,true),(14,true)]
theorem der_52115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52115 :=
  CNF.rup_sound cl_52115 [cl_575,cl_37568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_575 v h) (hints_cons _ _ _ (der_37568 v h) (by intro d hd; cases hd)))
def cl_52116 : CNF.NClause := [(70,false),(88,false),(76,true),(64,false),(83,false),(48,false)]
theorem der_52116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52116 :=
  CNF.rup_sound cl_52116 [cl_26339,cl_33166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26339 v h) (hints_cons _ _ _ (der_33166 v h) (by intro d hd; cases hd)))
def cl_52117 : CNF.NClause := [(70,false),(77,false),(88,false),(64,false),(48,false),(83,true)]
theorem der_52117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52117 :=
  CNF.rup_sound cl_52117 [cl_26340,cl_51010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26340 v h) (hints_cons _ _ _ (der_51010 v h) (by intro d hd; cases hd)))
def cl_52118 : CNF.NClause := [(70,false),(88,false),(64,false),(76,false),(48,false),(83,true)]
theorem der_52118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52118 :=
  CNF.rup_sound cl_52118 [cl_26341,cl_33183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26341 v h) (hints_cons _ _ _ (der_33183 v h) (by intro d hd; cases hd)))
def cl_52119 : CNF.NClause := [(17,true),(70,false),(77,false),(64,false),(83,false),(48,false)]
theorem der_52119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52119 :=
  CNF.rup_sound cl_52119 [cl_26343,cl_33195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26343 v h) (hints_cons _ _ _ (der_33195 v h) (by intro d hd; cases hd)))
def cl_52127 : CNF.NClause := [(82,false),(76,true),(8,false),(39,false),(79,false),(90,false)]
theorem der_52127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52127 :=
  CNF.rup_sound cl_52127 [cl_26373,cl_32109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26373 v h) (hints_cons _ _ _ (der_32109 v h) (by intro d hd; cases hd)))
def cl_52128 : CNF.NClause := [(65,false),(82,false),(68,false),(90,false),(79,true),(39,false)]
theorem der_52128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52128 :=
  CNF.rup_sound cl_52128 [cl_34883,cl_50596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34883 v h) (hints_cons _ _ _ (der_50596 v h) (by intro d hd; cases hd)))
def cl_52132 : CNF.NClause := [(82,false),(68,false),(39,false),(79,true),(65,false),(8,false)]
theorem der_52132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52132 :=
  CNF.rup_sound cl_52132 [cl_26384,cl_32161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26384 v h) (hints_cons _ _ _ (der_32161 v h) (by intro d hd; cases hd)))
def cl_52134 : CNF.NClause := [(76,false),(65,false),(39,false),(68,false),(90,false),(82,true)]
theorem der_52134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52134 :=
  CNF.rup_sound cl_52134 [cl_26392,cl_32131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26392 v h) (hints_cons _ _ _ (der_32131 v h) (by intro d hd; cases hd)))
def cl_52135 : CNF.NClause := [(68,true),(65,false),(79,false),(76,false),(39,false),(90,false)]
theorem der_52135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52135 :=
  CNF.rup_sound cl_52135 [cl_26395,cl_50601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26395 v h) (hints_cons _ _ _ (der_50601 v h) (by intro d hd; cases hd)))
def cl_52136 : CNF.NClause := [(68,true),(76,false),(79,false),(39,false),(90,false),(82,true)]
theorem der_52136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52136 :=
  CNF.rup_sound cl_52136 [cl_26397,cl_50601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26397 v h) (hints_cons _ _ _ (der_50601 v h) (by intro d hd; cases hd)))
def cl_52137 : CNF.NClause := [(8,false),(39,false),(79,false),(76,true),(90,false),(68,false)]
theorem der_52137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52137 :=
  CNF.rup_sound cl_52137 [cl_26399,cl_50619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26399 v h) (hints_cons _ _ _ (der_50619 v h) (by intro d hd; cases hd)))
def cl_52140 : CNF.NClause := [(65,false),(76,false),(8,false),(39,false),(68,true),(82,true)]
theorem der_52140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52140 :=
  CNF.rup_sound cl_52140 [cl_26411,cl_50627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26411 v h) (hints_cons _ _ _ (der_50627 v h) (by intro d hd; cases hd)))
def cl_52142 : CNF.NClause := [(90,true),(79,false),(76,false),(68,false),(39,false),(8,false)]
theorem der_52142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52142 :=
  CNF.rup_sound cl_52142 [cl_34885,cl_52067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34885 v h) (hints_cons _ _ _ (der_52067 v h) (by intro d hd; cases hd)))
def cl_52143 : CNF.NClause := [(82,false),(79,false),(76,false),(8,true),(68,false),(39,false)]
theorem der_52143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52143 :=
  CNF.rup_sound cl_52143 [cl_26423,cl_50610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26423 v h) (hints_cons _ _ _ (der_50610 v h) (by intro d hd; cases hd)))
def cl_52146 : CNF.NClause := [(76,false),(8,false),(68,false),(65,false),(39,false),(82,true)]
theorem der_52146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52146 :=
  CNF.rup_sound cl_52146 [cl_26454,cl_32182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26454 v h) (hints_cons _ _ _ (der_32182 v h) (by intro d hd; cases hd)))
def cl_52147 : CNF.NClause := [(39,false),(68,false),(79,true),(8,false),(82,true),(90,true)]
theorem der_52147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52147 :=
  CNF.rup_sound cl_52147 [cl_26472,cl_50630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26472 v h) (hints_cons _ _ _ (der_50630 v h) (by intro d hd; cases hd)))
def cl_52149 : CNF.NClause := [(68,true),(82,true),(76,true),(79,true),(8,true),(39,false)]
theorem der_52149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52149 :=
  CNF.rup_sound cl_52149 [cl_26485,cl_50608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26485 v h) (hints_cons _ _ _ (der_50608 v h) (by intro d hd; cases hd)))
def cl_52150 : CNF.NClause := [(37,false),(78,false),(74,false),(82,false),(91,false),(66,true)]
theorem der_52150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52150 :=
  CNF.rup_sound cl_52150 [cl_26489,cl_50547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26489 v h) (hints_cons _ _ _ (der_50547 v h) (by intro d hd; cases hd)))
def cl_52151 : CNF.NClause := [(37,false),(78,false),(70,false),(74,true),(82,false),(6,false)]
theorem der_52151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52151 :=
  CNF.rup_sound cl_52151 [cl_34887,cl_50656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34887 v h) (hints_cons _ _ _ (der_50656 v h) (by intro d hd; cases hd)))
def cl_52153 : CNF.NClause := [(37,false),(78,true),(6,false),(74,false),(91,false),(66,false)]
theorem der_52153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52153 :=
  CNF.rup_sound cl_52153 [cl_34888,cl_50647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34888 v h) (hints_cons _ _ _ (der_50647 v h) (by intro d hd; cases hd)))
def cl_52155 : CNF.NClause := [(37,false),(70,true),(6,false),(74,false),(82,false),(91,false)]
theorem der_52155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52155 :=
  CNF.rup_sound cl_52155 [cl_26503,cl_50649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26503 v h) (hints_cons _ _ _ (der_50649 v h) (by intro d hd; cases hd)))
def cl_52157 : CNF.NClause := [(37,false),(78,false),(91,false),(82,true),(66,false),(6,false)]
theorem der_52157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52157 :=
  CNF.rup_sound cl_52157 [cl_26519,cl_50639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26519 v h) (hints_cons _ _ _ (der_50639 v h) (by intro d hd; cases hd)))
def cl_52158 : CNF.NClause := [(70,false),(91,true),(82,false),(37,false),(6,false),(74,false)]
theorem der_52158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52158 :=
  CNF.rup_sound cl_52158 [cl_34890,cl_50653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34890 v h) (hints_cons _ _ _ (der_50653 v h) (by intro d hd; cases hd)))
def cl_52159 : CNF.NClause := [(82,false),(78,false),(74,false),(66,true),(37,false),(70,false)]
theorem der_52159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52159 :=
  CNF.rup_sound cl_52159 [cl_26544,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26544 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def cl_52160 : CNF.NClause := [(70,false),(74,true),(82,false),(66,false),(37,false),(6,false)]
theorem der_52160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52160 :=
  CNF.rup_sound cl_52160 [cl_26550,cl_50654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26550 v h) (hints_cons _ _ _ (der_50654 v h) (by intro d hd; cases hd)))
def cl_52162 : CNF.NClause := [(37,false),(6,false),(70,false),(74,false),(78,true),(66,false)]
theorem der_52162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52162 :=
  CNF.rup_sound cl_52162 [cl_26558,cl_50669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26558 v h) (hints_cons _ _ _ (der_50669 v h) (by intro d hd; cases hd)))
def cl_52163 : CNF.NClause := [(78,true),(37,false),(91,true),(82,false),(66,false),(6,false)]
theorem der_52163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52163 :=
  CNF.rup_sound cl_52163 [cl_26562,cl_50672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26562 v h) (hints_cons _ _ _ (der_50672 v h) (by intro d hd; cases hd)))
def cl_52164 : CNF.NClause := [(70,true),(74,false),(6,true),(37,false),(91,true),(82,false)]
theorem der_52164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52164 :=
  CNF.rup_sound cl_52164 [cl_26565,cl_50547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26565 v h) (hints_cons _ _ _ (der_50547 v h) (by intro d hd; cases hd)))
def cl_52166 : CNF.NClause := [(70,false),(91,true),(66,false),(37,false),(78,true),(82,true)]
theorem der_52166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52166 :=
  CNF.rup_sound cl_52166 [cl_26591,cl_50670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26591 v h) (hints_cons _ _ _ (der_50670 v h) (by intro d hd; cases hd)))
def cl_52167 : CNF.NClause := [(70,true),(66,false),(6,true),(37,false),(74,false),(78,true)]
theorem der_52167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52167 :=
  CNF.rup_sound cl_52167 [cl_26595,cl_50643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26595 v h) (hints_cons _ _ _ (der_50643 v h) (by intro d hd; cases hd)))
def cl_52169 : CNF.NClause := [(83,true),(84,false),(92,false),(86,false),(82,false),(36,false)]
theorem der_52169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52169 :=
  CNF.rup_sound cl_52169 [cl_34891,cl_50699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34891 v h) (hints_cons _ _ _ (der_50699 v h) (by intro d hd; cases hd)))
def cl_52171 : CNF.NClause := [(83,true),(92,false),(36,false),(84,false),(5,false),(86,false)]
theorem der_52171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52171 :=
  CNF.rup_sound cl_52171 [cl_26609,cl_50682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26609 v h) (hints_cons _ _ _ (der_50682 v h) (by intro d hd; cases hd)))
def cl_52172 : CNF.NClause := [(92,false),(85,false),(36,false),(86,false),(83,false),(84,true)]
theorem der_52172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52172 :=
  CNF.rup_sound cl_52172 [cl_26612,cl_32285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26612 v h) (hints_cons _ _ _ (der_32285 v h) (by intro d hd; cases hd)))
def cl_52177 : CNF.NClause := [(92,false),(84,false),(36,false),(85,false),(82,false),(83,true)]
theorem der_52177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52177 :=
  CNF.rup_sound cl_52177 [cl_26636,cl_50681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26636 v h) (hints_cons _ _ _ (der_50681 v h) (by intro d hd; cases hd)))
def cl_52178 : CNF.NClause := [(82,false),(92,false),(86,true),(85,false),(36,false),(5,false)]
theorem der_52178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52178 :=
  CNF.rup_sound cl_52178 [cl_26640,cl_32302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26640 v h) (hints_cons _ _ _ (der_32302 v h) (by intro d hd; cases hd)))
def cl_52181 : CNF.NClause := [(85,true),(92,false),(36,false),(84,false),(83,false),(5,false)]
theorem der_52181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52181 :=
  CNF.rup_sound cl_52181 [cl_26650,cl_32307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26650 v h) (hints_cons _ _ _ (der_32307 v h) (by intro d hd; cases hd)))
def cl_52182 : CNF.NClause := [(92,false),(82,false),(86,true),(36,false),(84,true),(85,true)]
theorem der_52182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52182 :=
  CNF.rup_sound cl_52182 [cl_26657,cl_32315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26657 v h) (hints_cons _ _ _ (der_32315 v h) (by intro d hd; cases hd)))
def cl_52184 : CNF.NClause := [(84,false),(85,false),(92,true),(86,false),(36,false),(83,false)]
theorem der_52184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52184 :=
  CNF.rup_sound cl_52184 [cl_26665,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26665 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_52185 : CNF.NClause := [(84,false),(85,false),(92,true),(86,false),(82,false),(36,false)]
theorem der_52185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52185 :=
  CNF.rup_sound cl_52185 [cl_26667,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26667 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_52186 : CNF.NClause := [(83,true),(82,true),(86,false),(5,false),(36,false),(84,false)]
theorem der_52186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52186 :=
  CNF.rup_sound cl_52186 [cl_26669,cl_50687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26669 v h) (hints_cons _ _ _ (der_50687 v h) (by intro d hd; cases hd)))
def cl_52187 : CNF.NClause := [(83,false),(82,false),(86,false),(85,false),(36,false),(92,true)]
theorem der_52187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52187 :=
  CNF.rup_sound cl_52187 [cl_26671,cl_50693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26671 v h) (hints_cons _ _ _ (der_50693 v h) (by intro d hd; cases hd)))
def cl_52188 : CNF.NClause := [(85,false),(36,false),(86,false),(83,false),(84,true),(82,true)]
theorem der_52188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52188 :=
  CNF.rup_sound cl_52188 [cl_26674,cl_52172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26674 v h) (hints_cons _ _ _ (der_52172 v h) (by intro d hd; cases hd)))
def cl_52189 : CNF.NClause := [(83,true),(82,false),(85,false),(84,true),(5,false),(36,false)]
theorem der_52189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52189 :=
  CNF.rup_sound cl_52189 [cl_26675,cl_32342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26675 v h) (hints_cons _ _ _ (der_32342 v h) (by intro d hd; cases hd)))
def cl_52190 : CNF.NClause := [(84,false),(36,false),(86,false),(82,false),(92,true),(83,false)]
theorem der_52190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52190 :=
  CNF.rup_sound cl_52190 [cl_26679,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26679 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_52191 : CNF.NClause := [(85,true),(36,false),(84,false),(86,false),(5,false),(82,true)]
theorem der_52191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52191 :=
  CNF.rup_sound cl_52191 [cl_26681,cl_50701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26681 v h) (hints_cons _ _ _ (der_50701 v h) (by intro d hd; cases hd)))
def cl_52193 : CNF.NClause := [(86,false),(36,false),(82,false),(84,true),(85,true),(92,true)]
theorem der_52193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52193 :=
  CNF.rup_sound cl_52193 [cl_26688,cl_50688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26688 v h) (hints_cons _ _ _ (der_50688 v h) (by intro d hd; cases hd)))
def cl_52194 : CNF.NClause := [(84,false),(85,false),(92,true),(82,false),(36,false),(83,false)]
theorem der_52194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52194 :=
  CNF.rup_sound cl_52194 [cl_26695,cl_50690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26695 v h) (hints_cons _ _ _ (der_50690 v h) (by intro d hd; cases hd)))
def cl_52195 : CNF.NClause := [(84,false),(83,false),(85,false),(36,false),(86,true),(5,false)]
theorem der_52195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52195 :=
  CNF.rup_sound cl_52195 [cl_26697,cl_32346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26697 v h) (hints_cons _ _ _ (der_32346 v h) (by intro d hd; cases hd)))
def cl_52197 : CNF.NClause := [(85,false),(36,false),(86,true),(82,false),(83,false),(84,true)]
theorem der_52197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52197 :=
  CNF.rup_sound cl_52197 [cl_26703,cl_50694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26703 v h) (hints_cons _ _ _ (der_50694 v h) (by intro d hd; cases hd)))
def cl_52198 : CNF.NClause := [(83,false),(82,false),(36,false),(84,false),(85,true),(92,true)]
theorem der_52198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52198 :=
  CNF.rup_sound cl_52198 [cl_26712,cl_52190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26712 v h) (hints_cons _ _ _ (der_52190 v h) (by intro d hd; cases hd)))
def cl_52199 : CNF.NClause := [(67,false),(73,false),(52,false),(66,false),(21,false),(88,true)]
theorem der_52199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52199 :=
  CNF.rup_sound cl_52199 [cl_34894,cl_51765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34894 v h) (hints_cons _ _ _ (der_51765 v h) (by intro d hd; cases hd)))
def cl_52201 : CNF.NClause := [(65,false),(69,false),(73,false),(86,false),(77,true),(49,false)]
theorem der_52201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52201 :=
  CNF.rup_sound cl_52201 [cl_26728,cl_52022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26728 v h) (hints_cons _ _ _ (der_52022 v h) (by intro d hd; cases hd)))
def cl_52202 : CNF.NClause := [(83,false),(81,false),(23,true),(54,false),(89,false),(67,false)]
theorem der_52202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52202 :=
  CNF.rup_sound cl_52202 [cl_34896,cl_32537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34896 v h) (hints_cons _ _ _ (der_32537 v h) (by intro d hd; cases hd)))
def cl_52208 : CNF.NClause := [(88,false),(17,true),(77,false),(48,false),(64,false),(76,false)]
theorem der_52208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52208 :=
  CNF.rup_sound cl_52208 [cl_26759,cl_33174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26759 v h) (hints_cons _ _ _ (der_33174 v h) (by intro d hd; cases hd)))
def cl_52210 : CNF.NClause := [(77,true),(89,false),(47,false),(66,false),(84,false),(75,false)]
theorem der_52210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52210 :=
  CNF.rup_sound cl_52210 [cl_26763,cl_51624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26763 v h) (hints_cons _ _ _ (der_51624 v h) (by intro d hd; cases hd)))
def cl_52212 : CNF.NClause := [(82,false),(40,false),(69,false),(81,false),(63,false),(9,true)]
theorem der_52212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52212 :=
  CNF.rup_sound cl_52212 [cl_26782,cl_50847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26782 v h) (hints_cons _ _ _ (der_50847 v h) (by intro d hd; cases hd)))
def cl_52214 : CNF.NClause := [(89,false),(86,false),(79,false),(63,false),(14,true),(45,false)]
theorem der_52214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52214 :=
  CNF.rup_sound cl_52214 [cl_26810,cl_47228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26810 v h) (hints_cons _ _ _ (der_47228 v h) (by intro d hd; cases hd)))
def cl_52215 : CNF.NClause := [(85,false),(78,false),(58,false),(76,false),(89,false),(62,true)]
theorem der_52215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52215 :=
  CNF.rup_sound cl_52215 [cl_26827,cl_50743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26827 v h) (hints_cons _ _ _ (der_50743 v h) (by intro d hd; cases hd)))
def cl_52218 : CNF.NClause := [(89,false),(78,false),(69,false),(76,true),(27,false),(58,false)]
theorem der_52218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52218 :=
  CNF.rup_sound cl_52218 [cl_26832,cl_32469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26832 v h) (hints_cons _ _ _ (der_32469 v h) (by intro d hd; cases hd)))
def cl_52219 : CNF.NClause := [(58,false),(78,false),(85,false),(27,false),(69,true),(62,false)]
theorem der_52219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52219 :=
  CNF.rup_sound cl_52219 [cl_26834,cl_32517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26834 v h) (hints_cons _ _ _ (der_32517 v h) (by intro d hd; cases hd)))
def cl_52220 : CNF.NClause := [(89,false),(69,false),(85,false),(76,true),(27,false),(58,false)]
theorem der_52220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52220 :=
  CNF.rup_sound cl_52220 [cl_26845,cl_32462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26845 v h) (hints_cons _ _ _ (der_32462 v h) (by intro d hd; cases hd)))
def cl_52222 : CNF.NClause := [(89,false),(78,false),(76,false),(58,false),(62,false),(85,true)]
theorem der_52222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52222 :=
  CNF.rup_sound cl_52222 [cl_26853,cl_50744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26853 v h) (hints_cons _ _ _ (der_50744 v h) (by intro d hd; cases hd)))
def cl_52223 : CNF.NClause := [(76,false),(69,false),(27,false),(58,false),(89,false),(85,true)]
theorem der_52223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52223 :=
  CNF.rup_sound cl_52223 [cl_26854,cl_50762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26854 v h) (hints_cons _ _ _ (der_50762 v h) (by intro d hd; cases hd)))
def cl_52224 : CNF.NClause := [(27,true),(78,false),(69,false),(58,false),(89,false),(62,true)]
theorem der_52224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52224 :=
  CNF.rup_sound cl_52224 [cl_26855,cl_50746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26855 v h) (hints_cons _ _ _ (der_50746 v h) (by intro d hd; cases hd)))
def cl_52225 : CNF.NClause := [(85,true),(76,true),(27,false),(89,false),(62,false),(58,false)]
theorem der_52225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52225 :=
  CNF.rup_sound cl_52225 [cl_26864,cl_50769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26864 v h) (hints_cons _ _ _ (der_50769 v h) (by intro d hd; cases hd)))
def cl_52227 : CNF.NClause := [(76,false),(69,false),(78,true),(58,false),(89,false),(62,false)]
theorem der_52227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52227 :=
  CNF.rup_sound cl_52227 [cl_26869,cl_50762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26869 v h) (hints_cons _ _ _ (der_50762 v h) (by intro d hd; cases hd)))
def cl_52228 : CNF.NClause := [(78,true),(89,false),(69,false),(27,false),(76,false),(58,false)]
theorem der_52228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52228 :=
  CNF.rup_sound cl_52228 [cl_26870,cl_32521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26870 v h) (hints_cons _ _ _ (der_32521 v h) (by intro d hd; cases hd)))
def cl_52229 : CNF.NClause := [(78,true),(89,false),(76,false),(58,false),(62,true),(85,true)]
theorem der_52229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52229 :=
  CNF.rup_sound cl_52229 [cl_26871,cl_50744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26871 v h) (hints_cons _ _ _ (der_50744 v h) (by intro d hd; cases hd)))
def cl_52232 : CNF.NClause := [(76,false),(27,false),(69,false),(85,false),(58,false),(89,true)]
theorem der_52232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52232 :=
  CNF.rup_sound cl_52232 [cl_26885,cl_50762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26885 v h) (hints_cons _ _ _ (der_50762 v h) (by intro d hd; cases hd)))
def cl_52234 : CNF.NClause := [(69,false),(85,false),(78,false),(58,false),(62,false),(89,true)]
theorem der_52234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52234 :=
  CNF.rup_sound cl_52234 [cl_26891,cl_50747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26891 v h) (hints_cons _ _ _ (der_50747 v h) (by intro d hd; cases hd)))
def cl_52235 : CNF.NClause := [(89,true),(78,true),(69,false),(76,false),(62,true),(58,false)]
theorem der_52235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52235 :=
  CNF.rup_sound cl_52235 [cl_26902,cl_32524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26902 v h) (hints_cons _ _ _ (der_32524 v h) (by intro d hd; cases hd)))
def cl_52236 : CNF.NClause := [(76,false),(58,false),(78,true),(85,false),(69,true),(62,false)]
theorem der_52236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52236 :=
  CNF.rup_sound cl_52236 [cl_26904,cl_50740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26904 v h) (hints_cons _ _ _ (der_50740 v h) (by intro d hd; cases hd)))
def cl_52237 : CNF.NClause := [(76,true),(85,false),(78,true),(27,true),(58,false),(89,true)]
theorem der_52237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52237 :=
  CNF.rup_sound cl_52237 [cl_26914,cl_50754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26914 v h) (hints_cons _ _ _ (der_50754 v h) (by intro d hd; cases hd)))
def cl_52238 : CNF.NClause := [(78,false),(69,false),(27,false),(58,false),(62,false),(85,true)]
theorem der_52238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52238 :=
  CNF.rup_sound cl_52238 [cl_26915,cl_32513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26915 v h) (hints_cons _ _ _ (der_32513 v h) (by intro d hd; cases hd)))
def cl_52240 : CNF.NClause := [(89,false),(54,false),(74,false),(81,false),(65,true),(23,false)]
theorem der_52240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52240 :=
  CNF.rup_sound cl_52240 [cl_34904,cl_32559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34904 v h) (hints_cons _ _ _ (der_32559 v h) (by intro d hd; cases hd)))
def cl_52241 : CNF.NClause := [(89,false),(54,false),(74,false),(81,false),(83,false),(65,true)]
theorem der_52241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52241 :=
  CNF.rup_sound cl_52241 [cl_26947,cl_50774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26947 v h) (hints_cons _ _ _ (der_50774 v h) (by intro d hd; cases hd)))
def cl_52242 : CNF.NClause := [(65,false),(89,false),(54,false),(74,false),(23,false),(67,true)]
theorem der_52242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52242 :=
  CNF.rup_sound cl_52242 [cl_34905,cl_32564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34905 v h) (hints_cons _ _ _ (der_32564 v h) (by intro d hd; cases hd)))
def cl_52244 : CNF.NClause := [(89,false),(54,false),(81,false),(83,false),(65,true),(23,false)]
theorem der_52244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52244 :=
  CNF.rup_sound cl_52244 [cl_26952,cl_32559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26952 v h) (hints_cons _ _ _ (der_32559 v h) (by intro d hd; cases hd)))
def cl_52246 : CNF.NClause := [(67,false),(89,false),(83,false),(81,true),(23,false),(54,false)]
theorem der_52246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52246 :=
  CNF.rup_sound cl_52246 [cl_34906,cl_50788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34906 v h) (hints_cons _ _ _ (der_50788 v h) (by intro d hd; cases hd)))
def cl_52249 : CNF.NClause := [(23,true),(81,false),(54,false),(74,false),(89,false),(65,false)]
theorem der_52249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52249 :=
  CNF.rup_sound cl_52249 [cl_26973,cl_32553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26973 v h) (hints_cons _ _ _ (der_32553 v h) (by intro d hd; cases hd)))
def cl_52251 : CNF.NClause := [(81,false),(74,false),(89,false),(54,false),(23,false),(67,true)]
theorem der_52251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52251 :=
  CNF.rup_sound cl_52251 [cl_26978,cl_32576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26978 v h) (hints_cons _ _ _ (der_32576 v h) (by intro d hd; cases hd)))
def cl_52253 : CNF.NClause := [(83,true),(81,true),(67,false),(23,true),(54,false),(65,true)]
theorem der_52253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52253 :=
  CNF.rup_sound cl_52253 [cl_26999,cl_50807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26999 v h) (hints_cons _ _ _ (der_50807 v h) (by intro d hd; cases hd)))
def cl_52254 : CNF.NClause := [(65,false),(83,false),(54,false),(74,false),(67,false),(89,true)]
theorem der_52254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52254 :=
  CNF.rup_sound cl_52254 [cl_34908,cl_50799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34908 v h) (hints_cons _ _ _ (der_50799 v h) (by intro d hd; cases hd)))
def cl_52256 : CNF.NClause := [(89,true),(81,false),(74,false),(67,false),(23,true),(54,false)]
theorem der_52256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52256 :=
  CNF.rup_sound cl_52256 [cl_27006,cl_50807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27006 v h) (hints_cons _ _ _ (der_50807 v h) (by intro d hd; cases hd)))
def cl_52257 : CNF.NClause := [(83,false),(74,false),(67,false),(54,false),(81,true),(23,false)]
theorem der_52257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52257 :=
  CNF.rup_sound cl_52257 [cl_27019,cl_50788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27019 v h) (hints_cons _ _ _ (der_50788 v h) (by intro d hd; cases hd)))
def cl_52258 : CNF.NClause := [(83,false),(81,true),(23,false),(54,false),(67,true),(89,true)]
theorem der_52258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52258 :=
  CNF.rup_sound cl_52258 [cl_27031,cl_50788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27031 v h) (hints_cons _ _ _ (der_50788 v h) (by intro d hd; cases hd)))
def cl_52259 : CNF.NClause := [(65,false),(89,true),(74,false),(23,false),(54,false),(81,false)]
theorem der_52259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52259 :=
  CNF.rup_sound cl_52259 [cl_27035,cl_32602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27035 v h) (hints_cons _ _ _ (der_32602 v h) (by intro d hd; cases hd)))
def cl_52260 : CNF.NClause := [(65,true),(23,true),(54,false),(81,false),(83,true),(89,true)]
theorem der_52260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52260 :=
  CNF.rup_sound cl_52260 [cl_27046,cl_50809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27046 v h) (hints_cons _ _ _ (der_50809 v h) (by intro d hd; cases hd)))
def cl_52261 : CNF.NClause := [(82,false),(40,false),(69,false),(81,false),(63,true),(9,false)]
theorem der_52261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52261 :=
  CNF.rup_sound cl_52261 [cl_34909,cl_32683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34909 v h) (hints_cons _ _ _ (der_32683 v h) (by intro d hd; cases hd)))
def cl_52263 : CNF.NClause := [(75,false),(40,false),(88,false),(81,false),(63,true),(9,false)]
theorem der_52263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52263 :=
  CNF.rup_sound cl_52263 [cl_27069,cl_50828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27069 v h) (hints_cons _ _ _ (der_50828 v h) (by intro d hd; cases hd)))
def cl_52265 : CNF.NClause := [(82,true),(63,false),(69,false),(81,false),(88,false),(40,false)]
theorem der_52265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52265 :=
  CNF.rup_sound cl_52265 [cl_34910,cl_50827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34910 v h) (hints_cons _ _ _ (der_50827 v h) (by intro d hd; cases hd)))
def cl_52266 : CNF.NClause := [(40,false),(69,false),(88,false),(81,false),(9,false),(82,true)]
theorem der_52266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52266 :=
  CNF.rup_sound cl_52266 [cl_27090,cl_50829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27090 v h) (hints_cons _ _ _ (der_50829 v h) (by intro d hd; cases hd)))
def cl_52267 : CNF.NClause := [(69,false),(63,true),(88,false),(40,false),(9,false),(82,true)]
theorem der_52267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52267 :=
  CNF.rup_sound cl_52267 [cl_27108,cl_52266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27108 v h) (hints_cons _ _ _ (der_52266 v h) (by intro d hd; cases hd)))
def cl_52268 : CNF.NClause := [(75,false),(63,false),(69,false),(40,false),(82,false),(88,true)]
theorem der_52268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52268 :=
  CNF.rup_sound cl_52268 [cl_34911,cl_52064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34911 v h) (hints_cons _ _ _ (der_52064 v h) (by intro d hd; cases hd)))
def cl_52269 : CNF.NClause := [(75,false),(69,false),(82,false),(40,false),(9,false),(88,true)]
theorem der_52269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52269 :=
  CNF.rup_sound cl_52269 [cl_27114,cl_50843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27114 v h) (hints_cons _ _ _ (der_50843 v h) (by intro d hd; cases hd)))
def cl_52270 : CNF.NClause := [(69,false),(81,false),(40,false),(82,false),(63,true),(88,true)]
theorem der_52270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52270 :=
  CNF.rup_sound cl_52270 [cl_27120,cl_47453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27120 v h) (hints_cons _ _ _ (der_47453 v h) (by intro d hd; cases hd)))
def cl_52271 : CNF.NClause := [(75,false),(63,false),(81,false),(82,true),(9,false),(40,false)]
theorem der_52271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52271 :=
  CNF.rup_sound cl_52271 [cl_27137,cl_50852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27137 v h) (hints_cons _ _ _ (der_50852 v h) (by intro d hd; cases hd)))
def cl_52272 : CNF.NClause := [(81,false),(40,false),(69,false),(9,false),(82,true),(88,true)]
theorem der_52272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52272 :=
  CNF.rup_sound cl_52272 [cl_27144,cl_32703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27144 v h) (hints_cons _ _ _ (der_32703 v h) (by intro d hd; cases hd)))
def cl_52273 : CNF.NClause := [(75,false),(40,false),(69,false),(63,false),(82,true),(88,true)]
theorem der_52273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52273 :=
  CNF.rup_sound cl_52273 [cl_27150,cl_52064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27150 v h) (hints_cons _ _ _ (der_52064 v h) (by intro d hd; cases hd)))
def cl_52277 : CNF.NClause := [(88,false),(68,true),(60,false),(80,false),(62,false),(29,false)]
theorem der_52277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52277 :=
  CNF.rup_sound cl_52277 [cl_34913,cl_50864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34913 v h) (hints_cons _ _ _ (der_50864 v h) (by intro d hd; cases hd)))
def cl_52278 : CNF.NClause := [(60,false),(88,false),(74,false),(86,false),(80,false),(29,true)]
theorem der_52278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52278 :=
  CNF.rup_sound cl_52278 [cl_27163,cl_32724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27163 v h) (hints_cons _ _ _ (der_32724 v h) (by intro d hd; cases hd)))
def cl_52279 : CNF.NClause := [(60,false),(88,false),(74,false),(86,false),(80,false),(62,true)]
theorem der_52279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52279 :=
  CNF.rup_sound cl_52279 [cl_27164,cl_52278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27164 v h) (hints_cons _ _ _ (der_52278 v h) (by intro d hd; cases hd)))
def cl_52280 : CNF.NClause := [(60,false),(88,false),(74,true),(80,false),(62,false),(29,false)]
theorem der_52280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52280 :=
  CNF.rup_sound cl_52280 [cl_27169,cl_32750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27169 v h) (hints_cons _ _ _ (der_32750 v h) (by intro d hd; cases hd)))
def cl_52281 : CNF.NClause := [(60,false),(88,false),(74,false),(86,false),(68,false),(62,true)]
theorem der_52281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52281 :=
  CNF.rup_sound cl_52281 [cl_27174,cl_37956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27174 v h) (hints_cons _ _ _ (der_37956 v h) (by intro d hd; cases hd)))
def cl_52282 : CNF.NClause := [(88,false),(62,false),(29,false),(74,false),(60,false),(68,true)]
theorem der_52282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52282 :=
  CNF.rup_sound cl_52282 [cl_27176,cl_32744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27176 v h) (hints_cons _ _ _ (der_32744 v h) (by intro d hd; cases hd)))
def cl_52284 : CNF.NClause := [(88,false),(68,true),(60,false),(74,false),(29,false),(80,true)]
theorem der_52284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52284 :=
  CNF.rup_sound cl_52284 [cl_27178,cl_50865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27178 v h) (hints_cons _ _ _ (der_50865 v h) (by intro d hd; cases hd)))
def cl_52286 : CNF.NClause := [(88,false),(60,false),(86,true),(80,false),(62,false),(29,false)]
theorem der_52286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52286 :=
  CNF.rup_sound cl_52286 [cl_34915,cl_32750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34915 v h) (hints_cons _ _ _ (der_32750 v h) (by intro d hd; cases hd)))
def cl_52287 : CNF.NClause := [(88,false),(80,false),(60,false),(74,false),(68,false),(62,true)]
theorem der_52287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52287 :=
  CNF.rup_sound cl_52287 [cl_27189,cl_50862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27189 v h) (hints_cons _ _ _ (der_50862 v h) (by intro d hd; cases hd)))
def cl_52288 : CNF.NClause := [(68,true),(88,false),(74,false),(60,false),(80,false),(86,true)]
theorem der_52288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52288 :=
  CNF.rup_sound cl_52288 [cl_27194,cl_50864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27194 v h) (hints_cons _ _ _ (der_50864 v h) (by intro d hd; cases hd)))
def cl_52290 : CNF.NClause := [(60,false),(80,false),(68,true),(88,false),(86,true),(29,true)]
theorem der_52290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52290 :=
  CNF.rup_sound cl_52290 [cl_27202,cl_52288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27202 v h) (hints_cons _ _ _ (der_52288 v h) (by intro d hd; cases hd)))
def cl_52291 : CNF.NClause := [(88,false),(74,false),(60,false),(86,true),(62,false),(29,false)]
theorem der_52291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52291 :=
  CNF.rup_sound cl_52291 [cl_27203,cl_32742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27203 v h) (hints_cons _ _ _ (der_32742 v h) (by intro d hd; cases hd)))
def cl_52292 : CNF.NClause := [(62,false),(68,true),(74,false),(60,false),(80,false),(29,false)]
theorem der_52292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52292 :=
  CNF.rup_sound cl_52292 [cl_27222,cl_50867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27222 v h) (hints_cons _ _ _ (der_50867 v h) (by intro d hd; cases hd)))
def cl_52293 : CNF.NClause := [(68,true),(62,true),(60,false),(74,false),(80,false),(86,false)]
theorem der_52293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52293 :=
  CNF.rup_sound cl_52293 [cl_27225,cl_52279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27225 v h) (hints_cons _ _ _ (der_52279 v h) (by intro d hd; cases hd)))
def cl_52295 : CNF.NClause := [(62,false),(60,false),(74,false),(68,false),(29,false),(88,true)]
theorem der_52295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52295 :=
  CNF.rup_sound cl_52295 [cl_27234,cl_32793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27234 v h) (hints_cons _ _ _ (der_32793 v h) (by intro d hd; cases hd)))
def cl_52296 : CNF.NClause := [(60,false),(74,false),(86,true),(80,false),(62,false),(29,false)]
theorem der_52296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52296 :=
  CNF.rup_sound cl_52296 [cl_27250,cl_50867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27250 v h) (hints_cons _ _ _ (der_50867 v h) (by intro d hd; cases hd)))
def cl_52297 : CNF.NClause := [(80,true),(62,false),(60,false),(74,false),(86,true),(88,true)]
theorem der_52297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52297 :=
  CNF.rup_sound cl_52297 [cl_27267,cl_50868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27267 v h) (hints_cons _ _ _ (der_50868 v h) (by intro d hd; cases hd)))
def cl_52298 : CNF.NClause := [(60,false),(80,true),(68,true),(86,true),(29,false),(88,true)]
theorem der_52298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52298 :=
  CNF.rup_sound cl_52298 [cl_27280,cl_50867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27280 v h) (hints_cons _ _ _ (der_50867 v h) (by intro d hd; cases hd)))
def cl_52299 : CNF.NClause := [(91,false),(76,false),(67,false),(55,false),(84,false),(63,true)]
theorem der_52299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52299 :=
  CNF.rup_sound cl_52299 [cl_27282,cl_32816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27282 v h) (hints_cons _ _ _ (der_32816 v h) (by intro d hd; cases hd)))
def cl_52300 : CNF.NClause := [(91,false),(63,false),(76,false),(80,false),(55,false),(67,true)]
theorem der_52300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52300 :=
  CNF.rup_sound cl_52300 [cl_27283,cl_50886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27283 v h) (hints_cons _ _ _ (der_50886 v h) (by intro d hd; cases hd)))
def cl_52301 : CNF.NClause := [(84,false),(76,false),(80,false),(55,false),(24,false),(63,true)]
theorem der_52301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52301 :=
  CNF.rup_sound cl_52301 [cl_27284,cl_50888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27284 v h) (hints_cons _ _ _ (der_50888 v h) (by intro d hd; cases hd)))
def cl_52302 : CNF.NClause := [(76,true),(55,false),(84,false),(67,false),(91,false),(24,false)]
theorem der_52302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52302 :=
  CNF.rup_sound cl_52302 [cl_27287,cl_32819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27287 v h) (hints_cons _ _ _ (der_32819 v h) (by intro d hd; cases hd)))
def cl_52304 : CNF.NClause := [(80,false),(55,false),(84,false),(24,false),(63,true),(67,true)]
theorem der_52304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52304 :=
  CNF.rup_sound cl_52304 [cl_27291,cl_32852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27291 v h) (hints_cons _ _ _ (der_32852 v h) (by intro d hd; cases hd)))
def cl_52305 : CNF.NClause := [(76,false),(84,false),(55,false),(67,false),(91,false),(80,true)]
theorem der_52305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52305 :=
  CNF.rup_sound cl_52305 [cl_34919,cl_52017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34919 v h) (hints_cons _ _ _ (der_52017 v h) (by intro d hd; cases hd)))
def cl_52309 : CNF.NClause := [(67,false),(55,false),(76,false),(91,false),(84,true),(24,false)]
theorem der_52309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52309 :=
  CNF.rup_sound cl_52309 [cl_27309,cl_32831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27309 v h) (hints_cons _ _ _ (der_32831 v h) (by intro d hd; cases hd)))
def cl_52312 : CNF.NClause := [(67,false),(55,false),(91,false),(84,true),(24,false),(63,true)]
theorem der_52312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52312 :=
  CNF.rup_sound cl_52312 [cl_27317,cl_32839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27317 v h) (hints_cons _ _ _ (der_32839 v h) (by intro d hd; cases hd)))
def cl_52313 : CNF.NClause := [(67,false),(24,true),(55,false),(63,false),(91,false),(84,true)]
theorem der_52313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52313 :=
  CNF.rup_sound cl_52313 [cl_27324,cl_50878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27324 v h) (hints_cons _ _ _ (der_50878 v h) (by intro d hd; cases hd)))
def cl_52315 : CNF.NClause := [(67,false),(76,false),(84,false),(91,true),(80,false),(55,false)]
theorem der_52315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52315 :=
  CNF.rup_sound cl_52315 [cl_34920,cl_50879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34920 v h) (hints_cons _ _ _ (der_50879 v h) (by intro d hd; cases hd)))
def cl_52316 : CNF.NClause := [(67,false),(55,false),(84,false),(76,false),(24,false),(63,true)]
theorem der_52316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52316 :=
  CNF.rup_sound cl_52316 [cl_27340,cl_32856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27340 v h) (hints_cons _ _ _ (der_32856 v h) (by intro d hd; cases hd)))
def cl_52317 : CNF.NClause := [(80,false),(84,false),(76,false),(55,false),(24,false),(91,true)]
theorem der_52317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52317 :=
  CNF.rup_sound cl_52317 [cl_27344,cl_44209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27344 v h) (hints_cons _ _ _ (der_44209 v h) (by intro d hd; cases hd)))
def cl_52318 : CNF.NClause := [(76,true),(80,false),(55,false),(63,false),(84,false),(24,false)]
theorem der_52318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52318 :=
  CNF.rup_sound cl_52318 [cl_27346,cl_32878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27346 v h) (hints_cons _ _ _ (der_32878 v h) (by intro d hd; cases hd)))
def cl_52319 : CNF.NClause := [(84,false),(24,false),(63,false),(67,false),(55,false),(80,true)]
theorem der_52319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52319 :=
  CNF.rup_sound cl_52319 [cl_27354,cl_50896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27354 v h) (hints_cons _ _ _ (der_50896 v h) (by intro d hd; cases hd)))
def cl_52322 : CNF.NClause := [(55,false),(76,true),(80,false),(84,true),(24,true),(67,true)]
theorem der_52322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52322 :=
  CNF.rup_sound cl_52322 [cl_27385,cl_50878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27385 v h) (hints_cons _ _ _ (der_50878 v h) (by intro d hd; cases hd)))
def cl_52324 : CNF.NClause := [(76,false),(80,true),(24,true),(55,false),(84,true),(67,true)]
theorem der_52324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52324 :=
  CNF.rup_sound cl_52324 [cl_27391,cl_50892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27391 v h) (hints_cons _ _ _ (der_50892 v h) (by intro d hd; cases hd)))
def cl_52325 : CNF.NClause := [(46,false),(79,false),(81,false),(78,false),(80,false),(77,true)]
theorem der_52325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52325 :=
  CNF.rup_sound cl_52325 [cl_27402,cl_50910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27402 v h) (hints_cons _ _ _ (der_50910 v h) (by intro d hd; cases hd)))
def cl_52327 : CNF.NClause := [(80,false),(46,false),(15,false),(81,false),(92,false),(79,true)]
theorem der_52327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52327 :=
  CNF.rup_sound cl_52327 [cl_34921,cl_32908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34921 v h) (hints_cons _ _ _ (der_32908 v h) (by intro d hd; cases hd)))
def cl_52328 : CNF.NClause := [(15,true),(81,false),(78,false),(77,false),(46,false),(92,false)]
theorem der_52328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52328 :=
  CNF.rup_sound cl_52328 [cl_27406,cl_32905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27406 v h) (hints_cons _ _ _ (der_32905 v h) (by intro d hd; cases hd)))
def cl_52329 : CNF.NClause := [(46,false),(15,false),(81,false),(78,false),(80,false),(77,true)]
theorem der_52329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52329 :=
  CNF.rup_sound cl_52329 [cl_27407,cl_32938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27407 v h) (hints_cons _ _ _ (der_32938 v h) (by intro d hd; cases hd)))
def cl_52332 : CNF.NClause := [(46,false),(78,true),(77,false),(15,false),(81,false),(92,false)]
theorem der_52332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52332 :=
  CNF.rup_sound cl_52332 [cl_27416,cl_50908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27416 v h) (hints_cons _ _ _ (der_50908 v h) (by intro d hd; cases hd)))
def cl_52333 : CNF.NClause := [(92,false),(46,false),(15,false),(81,false),(78,false),(80,true)]
theorem der_52333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52333 :=
  CNF.rup_sound cl_52333 [cl_27420,cl_32904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27420 v h) (hints_cons _ _ _ (der_32904 v h) (by intro d hd; cases hd)))
def cl_52337 : CNF.NClause := [(80,false),(46,false),(77,false),(15,false),(78,false),(79,true)]
theorem der_52337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52337 :=
  CNF.rup_sound cl_52337 [cl_27435,cl_32963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27435 v h) (hints_cons _ _ _ (der_32963 v h) (by intro d hd; cases hd)))
def cl_52338 : CNF.NClause := [(81,true),(15,false),(92,false),(80,false),(46,false),(79,true)]
theorem der_52338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52338 :=
  CNF.rup_sound cl_52338 [cl_27439,cl_50903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27439 v h) (hints_cons _ _ _ (der_50903 v h) (by intro d hd; cases hd)))
def cl_52340 : CNF.NClause := [(81,true),(46,false),(77,false),(80,true),(78,false),(79,true)]
theorem der_52340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52340 :=
  CNF.rup_sound cl_52340 [cl_27451,cl_32979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27451 v h) (hints_cons _ _ _ (der_32979 v h) (by intro d hd; cases hd)))
def cl_52341 : CNF.NClause := [(46,false),(79,false),(15,false),(81,false),(78,false),(92,true)]
theorem der_52341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52341 :=
  CNF.rup_sound cl_52341 [cl_27458,cl_52039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27458 v h) (hints_cons _ _ _ (der_52039 v h) (by intro d hd; cases hd)))
def cl_52342 : CNF.NClause := [(46,false),(79,false),(77,false),(81,false),(78,false),(92,true)]
theorem der_52342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52342 :=
  CNF.rup_sound cl_52342 [cl_27459,cl_52039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27459 v h) (hints_cons _ _ _ (der_52039 v h) (by intro d hd; cases hd)))
def cl_52344 : CNF.NClause := [(46,false),(81,false),(80,false),(79,true),(15,true),(92,true)]
theorem der_52344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52344 :=
  CNF.rup_sound cl_52344 [cl_27472,cl_50911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27472 v h) (hints_cons _ _ _ (der_50911 v h) (by intro d hd; cases hd)))
def cl_52345 : CNF.NClause := [(46,false),(78,false),(77,false),(15,false),(81,false),(92,true)]
theorem der_52345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52345 :=
  CNF.rup_sound cl_52345 [cl_27480,cl_52342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27480 v h) (hints_cons _ _ _ (der_52342 v h) (by intro d hd; cases hd)))
def cl_52346 : CNF.NClause := [(46,false),(79,true),(78,true),(81,false),(15,true),(92,true)]
theorem der_52346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52346 :=
  CNF.rup_sound cl_52346 [cl_27487,cl_52344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27487 v h) (hints_cons _ _ _ (der_52344 v h) (by intro d hd; cases hd)))
def cl_52347 : CNF.NClause := [(79,false),(78,false),(46,false),(15,false),(80,false),(81,true)]
theorem der_52347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52347 :=
  CNF.rup_sound cl_52347 [cl_27488,cl_50919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27488 v h) (hints_cons _ _ _ (der_50919 v h) (by intro d hd; cases hd)))
def cl_52349 : CNF.NClause := [(80,false),(11,true),(72,false),(42,false),(83,false),(90,false)]
theorem der_52349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52349 :=
  CNF.rup_sound cl_52349 [cl_34923,cl_33000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34923 v h) (hints_cons _ _ _ (der_33000 v h) (by intro d hd; cases hd)))
def cl_52350 : CNF.NClause := [(83,false),(69,false),(80,false),(42,false),(90,false),(66,true)]
theorem der_52350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52350 :=
  CNF.rup_sound cl_52350 [cl_27519,cl_50930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27519 v h) (hints_cons _ _ _ (der_50930 v h) (by intro d hd; cases hd)))
def cl_52352 : CNF.NClause := [(42,false),(80,false),(83,false),(90,false),(11,false),(66,true)]
theorem der_52352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52352 :=
  CNF.rup_sound cl_52352 [cl_27521,cl_50930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27521 v h) (hints_cons _ _ _ (der_50930 v h) (by intro d hd; cases hd)))
def cl_52353 : CNF.NClause := [(69,false),(42,false),(80,false),(90,false),(11,false),(72,true)]
theorem der_52353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52353 :=
  CNF.rup_sound cl_52353 [cl_34924,cl_50944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34924 v h) (hints_cons _ _ _ (der_50944 v h) (by intro d hd; cases hd)))
def cl_52355 : CNF.NClause := [(83,false),(72,false),(42,false),(90,false),(11,false),(80,true)]
theorem der_52355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52355 :=
  CNF.rup_sound cl_52355 [cl_34925,cl_33011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34925 v h) (hints_cons _ _ _ (der_33011 v h) (by intro d hd; cases hd)))
def cl_52357 : CNF.NClause := [(90,false),(42,false),(69,false),(72,false),(83,false),(80,true)]
theorem der_52357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52357 :=
  CNF.rup_sound cl_52357 [cl_27532,cl_52355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27532 v h) (hints_cons _ _ _ (der_52355 v h) (by intro d hd; cases hd)))
def cl_52360 : CNF.NClause := [(42,false),(69,true),(72,false),(83,false),(90,false),(66,true)]
theorem der_52360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52360 :=
  CNF.rup_sound cl_52360 [cl_27536,cl_50927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27536 v h) (hints_cons _ _ _ (der_50927 v h) (by intro d hd; cases hd)))
def cl_52361 : CNF.NClause := [(80,false),(90,false),(69,false),(72,false),(11,true),(42,false)]
theorem der_52361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52361 :=
  CNF.rup_sound cl_52361 [cl_27545,cl_32997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27545 v h) (hints_cons _ _ _ (der_32997 v h) (by intro d hd; cases hd)))
def cl_52362 : CNF.NClause := [(83,true),(42,false),(69,false),(80,false),(90,false),(72,true)]
theorem der_52362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52362 :=
  CNF.rup_sound cl_52362 [cl_27555,cl_52353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27555 v h) (hints_cons _ _ _ (der_52353 v h) (by intro d hd; cases hd)))
def cl_52365 : CNF.NClause := [(69,false),(42,false),(11,true),(66,false),(72,true),(83,true)]
theorem der_52365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52365 :=
  CNF.rup_sound cl_52365 [cl_27569,cl_50953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27569 v h) (hints_cons _ _ _ (der_50953 v h) (by intro d hd; cases hd)))
def cl_52367 : CNF.NClause := [(80,false),(69,false),(72,false),(42,false),(11,false),(90,true)]
theorem der_52367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52367 :=
  CNF.rup_sound cl_52367 [cl_34927,cl_50944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34927 v h) (hints_cons _ _ _ (der_50944 v h) (by intro d hd; cases hd)))
def cl_52368 : CNF.NClause := [(80,false),(69,false),(11,true),(72,false),(42,false),(83,false)]
theorem der_52368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52368 :=
  CNF.rup_sound cl_52368 [cl_27576,cl_33021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27576 v h) (hints_cons _ _ _ (der_33021 v h) (by intro d hd; cases hd)))
def cl_52369 : CNF.NClause := [(90,true),(42,false),(72,false),(80,false),(83,false),(69,true)]
theorem der_52369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52369 :=
  CNF.rup_sound cl_52369 [cl_27581,cl_50939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27581 v h) (hints_cons _ _ _ (der_50939 v h) (by intro d hd; cases hd)))
def cl_52371 : CNF.NClause := [(80,false),(66,false),(11,false),(42,false),(72,true),(90,true)]
theorem der_52371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52371 :=
  CNF.rup_sound cl_52371 [cl_27587,cl_50945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27587 v h) (hints_cons _ _ _ (der_50945 v h) (by intro d hd; cases hd)))
def cl_52372 : CNF.NClause := [(83,false),(72,false),(42,false),(11,false),(66,false),(90,true)]
theorem der_52372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52372 :=
  CNF.rup_sound cl_52372 [cl_27591,cl_50951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27591 v h) (hints_cons _ _ _ (der_50951 v h) (by intro d hd; cases hd)))
def cl_52373 : CNF.NClause := [(90,true),(42,false),(72,false),(83,false),(11,true),(66,true)]
theorem der_52373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52373 :=
  CNF.rup_sound cl_52373 [cl_27598,cl_50940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27598 v h) (hints_cons _ _ _ (der_50940 v h) (by intro d hd; cases hd)))
def cl_52376 : CNF.NClause := [(90,true),(42,false),(69,false),(72,false),(80,false),(83,true)]
theorem der_52376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52376 :=
  CNF.rup_sound cl_52376 [cl_27610,cl_50944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27610 v h) (hints_cons _ _ _ (der_50944 v h) (by intro d hd; cases hd)))
def cl_52377 : CNF.NClause := [(80,false),(11,true),(42,false),(66,false),(83,true),(90,true)]
theorem der_52377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52377 :=
  CNF.rup_sound cl_52377 [cl_27612,cl_50946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27612 v h) (hints_cons _ _ _ (der_50946 v h) (by intro d hd; cases hd)))
def cl_52378 : CNF.NClause := [(72,false),(42,false),(11,true),(69,true),(66,false),(80,true)]
theorem der_52378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52378 :=
  CNF.rup_sound cl_52378 [cl_27628,cl_52093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27628 v h) (hints_cons _ _ _ (der_52093 v h) (by intro d hd; cases hd)))
def cl_52382 : CNF.NClause := [(65,false),(75,false),(87,false),(85,false),(3,true),(34,false)]
theorem der_52382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52382 :=
  CNF.rup_sound cl_52382 [cl_27640,cl_33071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27640 v h) (hints_cons _ _ _ (der_33071 v h) (by intro d hd; cases hd)))
def cl_52383 : CNF.NClause := [(34,false),(3,false),(75,true),(85,false),(87,false),(70,false)]
theorem der_52383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52383 :=
  CNF.rup_sound cl_52383 [cl_34931,cl_50971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34931 v h) (hints_cons _ _ _ (der_50971 v h) (by intro d hd; cases hd)))
def cl_52386 : CNF.NClause := [(85,false),(34,false),(3,false),(70,true),(87,false),(75,true)]
theorem der_52386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52386 :=
  CNF.rup_sound cl_52386 [cl_27648,cl_50965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27648 v h) (hints_cons _ _ _ (der_50965 v h) (by intro d hd; cases hd)))
def cl_52391 : CNF.NClause := [(85,true),(65,false),(34,false),(87,false),(70,false),(3,false)]
theorem der_52391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52391 :=
  CNF.rup_sound cl_52391 [cl_27672,cl_33142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27672 v h) (hints_cons _ _ _ (der_33142 v h) (by intro d hd; cases hd)))
def cl_52392 : CNF.NClause := [(85,true),(80,false),(87,false),(70,false),(65,false),(34,false)]
theorem der_52392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52392 :=
  CNF.rup_sound cl_52392 [cl_27673,cl_33123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27673 v h) (hints_cons _ _ _ (der_33123 v h) (by intro d hd; cases hd)))
def cl_52395 : CNF.NClause := [(87,true),(65,false),(85,false),(3,false),(34,false),(75,false)]
theorem der_52395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52395 :=
  CNF.rup_sound cl_52395 [cl_34933,cl_50987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34933 v h) (hints_cons _ _ _ (der_50987 v h) (by intro d hd; cases hd)))
def cl_52396 : CNF.NClause := [(65,false),(3,true),(34,false),(75,false),(85,false),(70,false)]
theorem der_52396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52396 :=
  CNF.rup_sound cl_52396 [cl_27696,cl_50984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27696 v h) (hints_cons _ _ _ (der_50984 v h) (by intro d hd; cases hd)))
def cl_52399 : CNF.NClause := [(80,false),(3,false),(34,false),(85,false),(75,true),(65,false)]
theorem der_52399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52399 :=
  CNF.rup_sound cl_52399 [cl_27703,cl_33108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27703 v h) (hints_cons _ _ _ (der_33108 v h) (by intro d hd; cases hd)))
def cl_52400 : CNF.NClause := [(87,true),(85,false),(80,false),(75,true),(65,false),(34,false)]
theorem der_52400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52400 :=
  CNF.rup_sound cl_52400 [cl_27704,cl_33107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27704 v h) (hints_cons _ _ _ (der_33107 v h) (by intro d hd; cases hd)))
def cl_52401 : CNF.NClause := [(87,true),(85,false),(3,false),(80,false),(34,false),(75,true)]
theorem der_52401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52401 :=
  CNF.rup_sound cl_52401 [cl_27705,cl_33108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27705 v h) (hints_cons _ _ _ (der_33108 v h) (by intro d hd; cases hd)))
def cl_52403 : CNF.NClause := [(65,false),(85,false),(3,false),(34,false),(75,true),(87,true)]
theorem der_52403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52403 :=
  CNF.rup_sound cl_52403 [cl_27719,cl_50976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27719 v h) (hints_cons _ _ _ (der_50976 v h) (by intro d hd; cases hd)))
def cl_52404 : CNF.NClause := [(65,true),(75,true),(80,true),(70,false),(34,false),(85,false)]
theorem der_52404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52404 :=
  CNF.rup_sound cl_52404 [cl_27722,cl_50962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27722 v h) (hints_cons _ _ _ (der_50962 v h) (by intro d hd; cases hd)))
def cl_52405 : CNF.NClause := [(65,false),(3,false),(34,false),(75,false),(70,false),(85,true)]
theorem der_52405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52405 :=
  CNF.rup_sound cl_52405 [cl_27727,cl_50984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27727 v h) (hints_cons _ _ _ (der_50984 v h) (by intro d hd; cases hd)))
def cl_52406 : CNF.NClause := [(85,true),(87,true),(75,false),(80,false),(3,true),(34,false)]
theorem der_52406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52406 :=
  CNF.rup_sound cl_52406 [cl_27730,cl_50980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27730 v h) (hints_cons _ _ _ (der_50980 v h) (by intro d hd; cases hd)))
def cl_52407 : CNF.NClause := [(87,true),(34,false),(80,false),(75,true),(65,false),(3,false)]
theorem der_52407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52407 :=
  CNF.rup_sound cl_52407 [cl_27735,cl_50982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27735 v h) (hints_cons _ _ _ (der_50982 v h) (by intro d hd; cases hd)))
def cl_52408 : CNF.NClause := [(80,false),(65,false),(3,true),(34,false),(85,true),(87,true)]
theorem der_52408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52408 :=
  CNF.rup_sound cl_52408 [cl_27740,cl_52406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27740 v h) (hints_cons _ _ _ (der_52406 v h) (by intro d hd; cases hd)))
def cl_52409 : CNF.NClause := [(65,false),(75,false),(3,true),(34,false),(85,true),(87,true)]
theorem der_52409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52409 :=
  CNF.rup_sound cl_52409 [cl_27748,cl_52406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27748 v h) (hints_cons _ _ _ (der_52406 v h) (by intro d hd; cases hd)))
def cl_52410 : CNF.NClause := [(87,true),(75,true),(34,false),(70,false),(85,true),(80,true)]
theorem der_52410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52410 :=
  CNF.rup_sound cl_52410 [cl_27752,cl_33144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27752 v h) (hints_cons _ _ _ (der_33144 v h) (by intro d hd; cases hd)))
def cl_52411 : CNF.NClause := [(85,true),(87,true),(75,true),(65,false),(3,false),(34,false)]
theorem der_52411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52411 :=
  CNF.rup_sound cl_52411 [cl_27755,cl_52407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27755 v h) (hints_cons _ _ _ (der_52407 v h) (by intro d hd; cases hd)))
def cl_52412 : CNF.NClause := [(70,true),(77,false),(88,false),(48,false),(76,false),(83,false)]
theorem der_52412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52412 :=
  CNF.rup_sound cl_52412 [cl_27760,cl_35090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27760 v h) (hints_cons _ _ _ (der_35090 v h) (by intro d hd; cases hd)))
def cl_52413 : CNF.NClause := [(70,false),(88,false),(76,true),(83,false),(48,false),(17,false)]
theorem der_52413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52413 :=
  CNF.rup_sound cl_52413 [cl_27764,cl_51020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27764 v h) (hints_cons _ _ _ (der_51020 v h) (by intro d hd; cases hd)))
def cl_52414 : CNF.NClause := [(83,false),(70,true),(88,false),(64,false),(48,false),(17,false)]
theorem der_52414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52414 :=
  CNF.rup_sound cl_52414 [cl_27766,cl_51029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27766 v h) (hints_cons _ _ _ (der_51029 v h) (by intro d hd; cases hd)))
def cl_52415 : CNF.NClause := [(88,false),(77,true),(76,false),(83,false),(17,false),(48,false)]
theorem der_52415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52415 :=
  CNF.rup_sound cl_52415 [cl_27770,cl_33187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27770 v h) (hints_cons _ _ _ (der_33187 v h) (by intro d hd; cases hd)))
def cl_52416 : CNF.NClause := [(77,true),(88,false),(76,true),(83,false),(64,true),(48,false)]
theorem der_52416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52416 :=
  CNF.rup_sound cl_52416 [cl_27782,cl_51020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27782 v h) (hints_cons _ _ _ (der_51020 v h) (by intro d hd; cases hd)))
def cl_52417 : CNF.NClause := [(77,false),(88,false),(64,false),(76,false),(48,false),(83,true)]
theorem der_52417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52417 :=
  CNF.rup_sound cl_52417 [cl_27783,cl_33172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27783 v h) (hints_cons _ _ _ (der_33172 v h) (by intro d hd; cases hd)))
def cl_52419 : CNF.NClause := [(88,false),(77,true),(48,false),(76,true),(64,true),(17,true)]
theorem der_52419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52419 :=
  CNF.rup_sound cl_52419 [cl_27810,cl_52416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27810 v h) (hints_cons _ _ _ (der_52416 v h) (by intro d hd; cases hd)))
def cl_52420 : CNF.NClause := [(83,false),(64,false),(76,false),(48,false),(17,false),(88,true)]
theorem der_52420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52420 :=
  CNF.rup_sound cl_52420 [cl_34935,cl_51027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34935 v h) (hints_cons _ _ _ (der_51027 v h) (by intro d hd; cases hd)))
def cl_52421 : CNF.NClause := [(77,false),(48,false),(83,false),(70,false),(64,true),(17,false)]
theorem der_52421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52421 :=
  CNF.rup_sound cl_52421 [cl_27812,cl_51019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27812 v h) (hints_cons _ _ _ (der_51019 v h) (by intro d hd; cases hd)))
def cl_52422 : CNF.NClause := [(70,true),(77,false),(48,false),(76,false),(83,false),(17,false)]
theorem der_52422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52422 :=
  CNF.rup_sound cl_52422 [cl_27814,cl_33196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27814 v h) (hints_cons _ _ _ (der_33196 v h) (by intro d hd; cases hd)))
def cl_52425 : CNF.NClause := [(77,true),(64,false),(76,false),(83,false),(17,false),(48,false)]
theorem der_52425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52425 :=
  CNF.rup_sound cl_52425 [cl_27825,cl_51029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27825 v h) (hints_cons _ _ _ (der_51029 v h) (by intro d hd; cases hd)))
def cl_52426 : CNF.NClause := [(76,true),(17,true),(48,false),(70,false),(64,true),(83,true)]
theorem der_52426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52426 :=
  CNF.rup_sound cl_52426 [cl_27849,cl_33241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27849 v h) (hints_cons _ _ _ (der_33241 v h) (by intro d hd; cases hd)))
def cl_52427 : CNF.NClause := [(76,false),(48,false),(70,false),(64,true),(83,true),(88,true)]
theorem der_52427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52427 :=
  CNF.rup_sound cl_52427 [cl_27856,cl_51025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27856 v h) (hints_cons _ _ _ (der_51025 v h) (by intro d hd; cases hd)))
def cl_52429 : CNF.NClause := [(85,false),(91,false),(68,false),(43,false),(81,false),(12,true)]
theorem der_52429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52429 :=
  CNF.rup_sound cl_52429 [cl_34936,cl_44340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34936 v h) (hints_cons _ _ _ (der_44340 v h) (by intro d hd; cases hd)))
def cl_52430 : CNF.NClause := [(91,false),(81,false),(43,false),(64,true),(85,false),(68,false)]
theorem der_52430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52430 :=
  CNF.rup_sound cl_52430 [cl_27868,cl_51037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27868 v h) (hints_cons _ _ _ (der_51037 v h) (by intro d hd; cases hd)))
def cl_52431 : CNF.NClause := [(91,false),(43,false),(68,true),(72,false),(81,false),(64,false)]
theorem der_52431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52431 :=
  CNF.rup_sound cl_52431 [cl_27869,cl_33313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27869 v h) (hints_cons _ _ _ (der_33313 v h) (by intro d hd; cases hd)))
def cl_52432 : CNF.NClause := [(91,false),(43,false),(64,true),(81,false),(85,false),(12,false)]
theorem der_52432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52432 :=
  CNF.rup_sound cl_52432 [cl_27870,cl_51037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27870 v h) (hints_cons _ _ _ (der_51037 v h) (by intro d hd; cases hd)))
def cl_52435 : CNF.NClause := [(81,true),(85,false),(91,false),(43,false),(72,false),(68,false)]
theorem der_52435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52435 :=
  CNF.rup_sound cl_52435 [cl_27879,cl_51062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27879 v h) (hints_cons _ _ _ (der_51062 v h) (by intro d hd; cases hd)))
def cl_52437 : CNF.NClause := [(85,false),(64,false),(68,false),(91,false),(43,false),(72,true)]
theorem der_52437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52437 :=
  CNF.rup_sound cl_52437 [cl_27886,cl_51060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27886 v h) (hints_cons _ _ _ (der_51060 v h) (by intro d hd; cases hd)))
def cl_52438 : CNF.NClause := [(85,true),(91,false),(43,false),(72,false),(64,false),(12,false)]
theorem der_52438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52438 :=
  CNF.rup_sound cl_52438 [cl_34938,cl_33327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34938 v h) (hints_cons _ _ _ (der_33327 v h) (by intro d hd; cases hd)))
def cl_52442 : CNF.NClause := [(81,true),(91,false),(43,false),(72,false),(68,false),(12,false)]
theorem der_52442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52442 :=
  CNF.rup_sound cl_52442 [cl_27909,cl_51043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27909 v h) (hints_cons _ _ _ (der_51043 v h) (by intro d hd; cases hd)))
def cl_52443 : CNF.NClause := [(81,true),(64,false),(43,false),(72,false),(91,false),(85,true)]
theorem der_52443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52443 :=
  CNF.rup_sound cl_52443 [cl_27914,cl_52438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27914 v h) (hints_cons _ _ _ (der_52438 v h) (by intro d hd; cases hd)))
def cl_52444 : CNF.NClause := [(81,true),(85,true),(12,true),(43,false),(68,false),(91,false)]
theorem der_52444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52444 :=
  CNF.rup_sound cl_52444 [cl_27918,cl_51046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27918 v h) (hints_cons _ _ _ (der_51046 v h) (by intro d hd; cases hd)))
def cl_52445 : CNF.NClause := [(91,true),(68,false),(43,false),(81,false),(85,false),(12,false)]
theorem der_52445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52445 :=
  CNF.rup_sound cl_52445 [cl_34939,cl_51051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34939 v h) (hints_cons _ _ _ (der_51051 v h) (by intro d hd; cases hd)))
def cl_52446 : CNF.NClause := [(68,true),(43,false),(12,false),(72,false),(81,false),(64,false)]
theorem der_52446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52446 :=
  CNF.rup_sound cl_52446 [cl_27928,cl_33313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27928 v h) (hints_cons _ _ _ (der_33313 v h) (by intro d hd; cases hd)))
def cl_52447 : CNF.NClause := [(12,false),(43,false),(81,false),(64,false),(85,false),(72,true)]
theorem der_52447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52447 :=
  CNF.rup_sound cl_52447 [cl_27932,cl_51072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27932 v h) (hints_cons _ _ _ (der_51072 v h) (by intro d hd; cases hd)))
def cl_52448 : CNF.NClause := [(81,true),(72,false),(64,false),(68,false),(43,false),(12,false)]
theorem der_52448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52448 :=
  CNF.rup_sound cl_52448 [cl_27940,cl_33327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27940 v h) (hints_cons _ _ _ (der_33327 v h) (by intro d hd; cases hd)))
def cl_52449 : CNF.NClause := [(91,true),(72,false),(64,false),(43,false),(81,true),(12,false)]
theorem der_52449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52449 :=
  CNF.rup_sound cl_52449 [cl_27944,cl_33328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27944 v h) (hints_cons _ _ _ (der_33328 v h) (by intro d hd; cases hd)))
def cl_52450 : CNF.NClause := [(72,false),(85,true),(43,false),(81,false),(68,false),(12,false)]
theorem der_52450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52450 :=
  CNF.rup_sound cl_52450 [cl_27956,cl_51067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27956 v h) (hints_cons _ _ _ (der_51067 v h) (by intro d hd; cases hd)))
def cl_52460 : CNF.NClause := [(69,false),(79,true),(33,false),(84,false),(74,false),(64,false)]
theorem der_52460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52460 :=
  CNF.rup_sound cl_52460 [cl_27999,cl_51109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27999 v h) (hints_cons _ _ _ (der_51109 v h) (by intro d hd; cases hd)))
def cl_52463 : CNF.NClause := [(87,false),(79,false),(33,false),(69,false),(64,false),(84,true)]
theorem der_52463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52463 :=
  CNF.rup_sound cl_52463 [cl_28014,cl_45654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28014 v h) (hints_cons _ _ _ (der_45654 v h) (by intro d hd; cases hd)))
def cl_52464 : CNF.NClause := [(87,false),(2,false),(79,false),(69,false),(64,true),(33,false)]
theorem der_52464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52464 :=
  CNF.rup_sound cl_52464 [cl_28015,cl_45654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28015 v h) (hints_cons _ _ _ (der_45654 v h) (by intro d hd; cases hd)))
def cl_52465 : CNF.NClause := [(87,false),(74,false),(84,true),(33,false),(79,false),(2,false)]
theorem der_52465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52465 :=
  CNF.rup_sound cl_52465 [cl_28017,cl_51088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28017 v h) (hints_cons _ _ _ (der_51088 v h) (by intro d hd; cases hd)))
def cl_52468 : CNF.NClause := [(87,true),(84,false),(33,false),(79,false),(69,false),(74,false)]
theorem der_52468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52468 :=
  CNF.rup_sound cl_52468 [cl_34942,cl_49698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34942 v h) (hints_cons _ _ _ (der_49698 v h) (by intro d hd; cases hd)))
def cl_52470 : CNF.NClause := [(84,false),(79,false),(33,false),(74,true),(69,false),(64,false)]
theorem der_52470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52470 :=
  CNF.rup_sound cl_52470 [cl_28051,cl_49698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28051 v h) (hints_cons _ _ _ (der_49698 v h) (by intro d hd; cases hd)))
def cl_52471 : CNF.NClause := [(64,false),(84,false),(33,false),(74,false),(79,true),(2,false)]
theorem der_52471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52471 :=
  CNF.rup_sound cl_52471 [cl_28059,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28059 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_52472 : CNF.NClause := [(79,false),(33,false),(84,true),(69,false),(64,false),(2,false)]
theorem der_52472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52472 :=
  CNF.rup_sound cl_52472 [cl_28075,cl_51117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28075 v h) (hints_cons _ _ _ (der_51117 v h) (by intro d hd; cases hd)))
def cl_52473 : CNF.NClause := [(64,true),(69,false),(33,false),(79,false),(2,false),(84,true)]
theorem der_52473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52473 :=
  CNF.rup_sound cl_52473 [cl_28085,cl_51087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28085 v h) (hints_cons _ _ _ (der_51087 v h) (by intro d hd; cases hd)))
def cl_52474 : CNF.NClause := [(87,true),(64,true),(33,false),(69,false),(74,false),(84,true)]
theorem der_52474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52474 :=
  CNF.rup_sound cl_52474 [cl_28093,cl_49699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28093 v h) (hints_cons _ _ _ (der_49699 v h) (by intro d hd; cases hd)))
def cl_52478 : CNF.NClause := [(80,false),(73,true),(82,false),(89,false),(38,false),(7,false)]
theorem der_52478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52478 :=
  CNF.rup_sound cl_52478 [cl_28114,cl_51132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28114 v h) (hints_cons _ _ _ (der_51132 v h) (by intro d hd; cases hd)))
def cl_52479 : CNF.NClause := [(89,false),(38,false),(80,false),(82,false),(64,true),(71,true)]
theorem der_52479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52479 :=
  CNF.rup_sound cl_52479 [cl_28116,cl_51142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28116 v h) (hints_cons _ _ _ (der_51142 v h) (by intro d hd; cases hd)))
def cl_52481 : CNF.NClause := [(89,false),(82,false),(73,false),(71,false),(7,true),(38,false)]
theorem der_52481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52481 :=
  CNF.rup_sound cl_52481 [cl_28118,cl_52044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28118 v h) (hints_cons _ _ _ (der_52044 v h) (by intro d hd; cases hd)))
def cl_52485 : CNF.NClause := [(80,false),(7,false),(38,false),(64,false),(89,false),(82,true)]
theorem der_52485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52485 :=
  CNF.rup_sound cl_52485 [cl_34946,cl_33450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34946 v h) (hints_cons _ _ _ (der_33450 v h) (by intro d hd; cases hd)))
def cl_52486 : CNF.NClause := [(80,false),(89,false),(64,false),(71,false),(7,true),(38,false)]
theorem der_52486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52486 :=
  CNF.rup_sound cl_52486 [cl_28133,cl_33447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28133 v h) (hints_cons _ _ _ (der_33447 v h) (by intro d hd; cases hd)))
def cl_52487 : CNF.NClause := [(80,false),(71,false),(38,false),(89,false),(64,true),(7,false)]
theorem der_52487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52487 :=
  CNF.rup_sound cl_52487 [cl_28134,cl_33495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28134 v h) (hints_cons _ _ _ (der_33495 v h) (by intro d hd; cases hd)))
def cl_52489 : CNF.NClause := [(89,false),(71,false),(73,true),(38,false),(64,false),(80,false)]
theorem der_52489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52489 :=
  CNF.rup_sound cl_52489 [cl_28140,cl_51133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28140 v h) (hints_cons _ _ _ (der_51133 v h) (by intro d hd; cases hd)))
def cl_52491 : CNF.NClause := [(89,false),(64,false),(38,false),(71,false),(80,true),(7,false)]
theorem der_52491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52491 :=
  CNF.rup_sound cl_52491 [cl_28148,cl_33457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28148 v h) (hints_cons _ _ _ (der_33457 v h) (by intro d hd; cases hd)))
def cl_52492 : CNF.NClause := [(89,false),(64,false),(38,false),(71,false),(80,true),(82,true)]
theorem der_52492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52492 :=
  CNF.rup_sound cl_52492 [cl_28149,cl_51135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28149 v h) (hints_cons _ _ _ (der_51135 v h) (by intro d hd; cases hd)))
def cl_52493 : CNF.NClause := [(73,false),(64,true),(71,false),(89,false),(7,true),(38,false)]
theorem der_52493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52493 :=
  CNF.rup_sound cl_52493 [cl_28151,cl_39150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28151 v h) (hints_cons _ _ _ (der_39150 v h) (by intro d hd; cases hd)))
def cl_52494 : CNF.NClause := [(89,true),(82,false),(38,false),(73,false),(80,false),(71,false)]
theorem der_52494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52494 :=
  CNF.rup_sound cl_52494 [cl_34947,cl_51144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34947 v h) (hints_cons _ _ _ (der_51144 v h) (by intro d hd; cases hd)))
def cl_52495 : CNF.NClause := [(82,false),(71,false),(64,false),(7,true),(38,false),(80,false)]
theorem der_52495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52495 :=
  CNF.rup_sound cl_52495 [cl_28164,cl_51146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28164 v h) (hints_cons _ _ _ (der_51146 v h) (by intro d hd; cases hd)))
def cl_52497 : CNF.NClause := [(73,false),(82,false),(38,false),(64,false),(80,false),(71,true)]
theorem der_52497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52497 :=
  CNF.rup_sound cl_52497 [cl_28167,cl_33466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28167 v h) (hints_cons _ _ _ (der_33466 v h) (by intro d hd; cases hd)))
def cl_52498 : CNF.NClause := [(89,true),(7,false),(64,false),(80,false),(71,true),(38,false)]
theorem der_52498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52498 :=
  CNF.rup_sound cl_52498 [cl_28175,cl_33509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28175 v h) (hints_cons _ _ _ (der_33509 v h) (by intro d hd; cases hd)))
def cl_52500 : CNF.NClause := [(80,false),(73,false),(64,false),(38,false),(7,false),(82,true)]
theorem der_52500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52500 :=
  CNF.rup_sound cl_52500 [cl_28195,cl_51152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28195 v h) (hints_cons _ _ _ (der_51152 v h) (by intro d hd; cases hd)))
def cl_52502 : CNF.NClause := [(80,false),(73,false),(38,false),(71,false),(7,false),(89,true)]
theorem der_52502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52502 :=
  CNF.rup_sound cl_52502 [cl_28197,cl_52494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28197 v h) (hints_cons _ _ _ (der_52494 v h) (by intro d hd; cases hd)))
def cl_52503 : CNF.NClause := [(80,false),(7,false),(38,false),(64,false),(71,false),(82,true)]
theorem der_52503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52503 :=
  CNF.rup_sound cl_52503 [cl_28203,cl_52485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28203 v h) (hints_cons _ _ _ (der_52485 v h) (by intro d hd; cases hd)))
def cl_52504 : CNF.NClause := [(73,false),(64,false),(38,false),(7,false),(82,true),(89,true)]
theorem der_52504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52504 :=
  CNF.rup_sound cl_52504 [cl_28211,cl_51152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28211 v h) (hints_cons _ _ _ (der_51152 v h) (by intro d hd; cases hd)))
def cl_52505 : CNF.NClause := [(71,false),(64,false),(7,true),(38,false),(80,true),(89,true)]
theorem der_52505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52505 :=
  CNF.rup_sound cl_52505 [cl_28212,cl_51153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28212 v h) (hints_cons _ _ _ (der_51153 v h) (by intro d hd; cases hd)))
def cl_52506 : CNF.NClause := [(64,true),(38,false),(7,true),(80,true),(82,true),(89,true)]
theorem der_52506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52506 :=
  CNF.rup_sound cl_52506 [cl_28222,cl_51157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28222 v h) (hints_cons _ _ _ (der_51157 v h) (by intro d hd; cases hd)))
def cl_52507 : CNF.NClause := [(62,true),(84,false),(81,false),(73,false),(90,false),(59,false)]
theorem der_52507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52507 :=
  CNF.rup_sound cl_52507 [cl_28228,cl_51165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28228 v h) (hints_cons _ _ _ (der_51165 v h) (by intro d hd; cases hd)))
def cl_52510 : CNF.NClause := [(73,true),(84,false),(59,false),(81,false),(90,false),(62,false)]
theorem der_52510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52510 :=
  CNF.rup_sound cl_52510 [cl_28232,cl_51173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28232 v h) (hints_cons _ _ _ (der_51173 v h) (by intro d hd; cases hd)))
def cl_52511 : CNF.NClause := [(62,true),(84,false),(81,false),(90,false),(28,false),(59,false)]
theorem der_52511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52511 :=
  CNF.rup_sound cl_52511 [cl_28233,cl_51165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28233 v h) (hints_cons _ _ _ (der_51165 v h) (by intro d hd; cases hd)))
def cl_52514 : CNF.NClause := [(90,false),(73,false),(84,false),(70,false),(81,true),(59,false)]
theorem der_52514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52514 :=
  CNF.rup_sound cl_52514 [cl_28239,cl_51181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28239 v h) (hints_cons _ _ _ (der_51181 v h) (by intro d hd; cases hd)))
def cl_52515 : CNF.NClause := [(59,false),(90,false),(73,false),(70,true),(84,false),(28,false)]
theorem der_52515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52515 :=
  CNF.rup_sound cl_52515 [cl_28242,cl_51169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28242 v h) (hints_cons _ _ _ (der_51169 v h) (by intro d hd; cases hd)))
def cl_52516 : CNF.NClause := [(62,false),(84,false),(73,true),(90,false),(28,false),(59,false)]
theorem der_52516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52516 :=
  CNF.rup_sound cl_52516 [cl_28246,cl_51172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28246 v h) (hints_cons _ _ _ (der_51172 v h) (by intro d hd; cases hd)))
def cl_52517 : CNF.NClause := [(62,false),(90,false),(59,false),(28,false),(81,false),(84,true)]
theorem der_52517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52517 :=
  CNF.rup_sound cl_52517 [cl_34949,cl_51172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34949 v h) (hints_cons _ _ _ (der_51172 v h) (by intro d hd; cases hd)))
def cl_52518 : CNF.NClause := [(62,false),(90,false),(59,false),(81,false),(70,false),(84,true)]
theorem der_52518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52518 :=
  CNF.rup_sound cl_52518 [cl_28254,cl_33533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28254 v h) (hints_cons _ _ _ (der_33533 v h) (by intro d hd; cases hd)))
def cl_52519 : CNF.NClause := [(62,true),(59,false),(73,false),(90,false),(28,false),(81,false)]
theorem der_52519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52519 :=
  CNF.rup_sound cl_52519 [cl_28255,cl_51165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28255 v h) (hints_cons _ _ _ (der_51165 v h) (by intro d hd; cases hd)))
def cl_52521 : CNF.NClause := [(81,true),(90,false),(28,false),(62,false),(59,false),(70,false)]
theorem der_52521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52521 :=
  CNF.rup_sound cl_52521 [cl_28269,cl_51200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28269 v h) (hints_cons _ _ _ (der_51200 v h) (by intro d hd; cases hd)))
def cl_52522 : CNF.NClause := [(81,false),(84,false),(59,false),(73,true),(28,false),(70,false)]
theorem der_52522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52522 :=
  CNF.rup_sound cl_52522 [cl_28291,cl_51177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28291 v h) (hints_cons _ _ _ (der_51177 v h) (by intro d hd; cases hd)))
def cl_52523 : CNF.NClause := [(81,true),(73,false),(28,false),(59,false),(84,false),(70,false)]
theorem der_52523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52523 :=
  CNF.rup_sound cl_52523 [cl_28298,cl_51183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28298 v h) (hints_cons _ _ _ (der_51183 v h) (by intro d hd; cases hd)))
def cl_52524 : CNF.NClause := [(90,true),(84,false),(59,false),(62,false),(81,true),(28,true)]
theorem der_52524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52524 :=
  CNF.rup_sound cl_52524 [cl_28309,cl_51184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28309 v h) (hints_cons _ _ _ (der_51184 v h) (by intro d hd; cases hd)))
def cl_52525 : CNF.NClause := [(62,false),(59,false),(28,false),(81,false),(70,false),(84,true)]
theorem der_52525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52525 :=
  CNF.rup_sound cl_52525 [cl_28312,cl_33584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28312 v h) (hints_cons _ _ _ (der_33584 v h) (by intro d hd; cases hd)))
def cl_52526 : CNF.NClause := [(62,true),(81,false),(59,false),(73,true),(84,true),(90,true)]
theorem der_52526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52526 :=
  CNF.rup_sound cl_52526 [cl_28324,cl_33589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28324 v h) (hints_cons _ _ _ (der_33589 v h) (by intro d hd; cases hd)))
def cl_52527 : CNF.NClause := [(90,true),(28,false),(84,true),(70,false),(59,false),(73,false)]
theorem der_52527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52527 :=
  CNF.rup_sound cl_52527 [cl_28326,cl_51195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28326 v h) (hints_cons _ _ _ (der_51195 v h) (by intro d hd; cases hd)))
def cl_52528 : CNF.NClause := [(90,true),(59,false),(62,false),(81,true),(84,true),(28,true)]
theorem der_52528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52528 :=
  CNF.rup_sound cl_52528 [cl_28337,cl_51197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28337 v h) (hints_cons _ _ _ (der_51197 v h) (by intro d hd; cases hd)))
def cl_52534 : CNF.NClause := [(92,false),(41,false),(72,false),(74,false),(76,false),(75,true)]
theorem der_52534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52534 :=
  CNF.rup_sound cl_52534 [cl_28352,cl_51261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28352 v h) (hints_cons _ _ _ (der_51261 v h) (by intro d hd; cases hd)))
def cl_52535 : CNF.NClause := [(73,true),(41,false),(72,false),(74,false),(76,false),(10,false)]
theorem der_52535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52535 :=
  CNF.rup_sound cl_52535 [cl_28355,cl_51231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28355 v h) (hints_cons _ _ _ (der_51231 v h) (by intro d hd; cases hd)))
def cl_52538 : CNF.NClause := [(75,true),(41,false),(72,false),(76,false),(10,false),(74,true)]
theorem der_52538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52538 :=
  CNF.rup_sound cl_52538 [cl_28363,cl_51244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28363 v h) (hints_cons _ _ _ (der_51244 v h) (by intro d hd; cases hd)))
def cl_52540 : CNF.NClause := [(75,false),(73,false),(76,true),(10,false),(41,false),(74,true)]
theorem der_52540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52540 :=
  CNF.rup_sound cl_52540 [cl_28376,cl_51255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28376 v h) (hints_cons _ _ _ (der_51255 v h) (by intro d hd; cases hd)))
def cl_52543 : CNF.NClause := [(73,false),(41,false),(92,true),(76,false),(75,false),(10,false)]
theorem der_52543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52543 :=
  CNF.rup_sound cl_52543 [cl_34951,cl_51251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34951 v h) (hints_cons _ _ _ (der_51251 v h) (by intro d hd; cases hd)))
def cl_52547 : CNF.NClause := [(72,false),(92,true),(76,true),(73,false),(41,false),(10,false)]
theorem der_52547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52547 :=
  CNF.rup_sound cl_52547 [cl_28445,cl_33698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28445 v h) (hints_cons _ _ _ (der_33698 v h) (by intro d hd; cases hd)))
def cl_52553 : CNF.NClause := [(68,true),(78,true),(73,true),(87,false),(35,false),(83,true)]
theorem der_52553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52553 :=
  CNF.rup_sound cl_52553 [cl_28518,cl_51314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28518 v h) (hints_cons _ _ _ (der_51314 v h) (by intro d hd; cases hd)))
def cl_52554 : CNF.NClause := [(83,false),(63,false),(78,false),(35,false),(4,false),(87,true)]
theorem der_52554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52554 :=
  CNF.rup_sound cl_52554 [cl_34953,cl_33755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34953 v h) (hints_cons _ _ _ (der_33755 v h) (by intro d hd; cases hd)))
def cl_52556 : CNF.NClause := [(73,true),(78,false),(4,true),(35,false),(83,false),(87,true)]
theorem der_52556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52556 :=
  CNF.rup_sound cl_52556 [cl_28530,cl_51293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28530 v h) (hints_cons _ _ _ (der_51293 v h) (by intro d hd; cases hd)))
def cl_52558 : CNF.NClause := [(78,true),(63,false),(35,false),(83,false),(68,false),(4,false)]
theorem der_52558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52558 :=
  CNF.rup_sound cl_52558 [cl_28541,cl_51285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28541 v h) (hints_cons _ _ _ (der_51285 v h) (by intro d hd; cases hd)))
def cl_52560 : CNF.NClause := [(68,true),(78,false),(4,true),(35,false),(63,false),(83,true)]
theorem der_52560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52560 :=
  CNF.rup_sound cl_52560 [cl_28562,cl_51278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28562 v h) (hints_cons _ _ _ (der_51278 v h) (by intro d hd; cases hd)))
def cl_52561 : CNF.NClause := [(63,true),(78,false),(73,true),(4,false),(35,false),(87,true)]
theorem der_52561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52561 :=
  CNF.rup_sound cl_52561 [cl_28563,cl_51293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28563 v h) (hints_cons _ _ _ (der_51293 v h) (by intro d hd; cases hd)))
def cl_52563 : CNF.NClause := [(68,true),(73,true),(35,false),(63,true),(83,true),(87,true)]
theorem der_52563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52563 :=
  CNF.rup_sound cl_52563 [cl_28579,cl_33797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28579 v h) (hints_cons _ _ _ (der_33797 v h) (by intro d hd; cases hd)))
def cl_52565 : CNF.NClause := [(62,true),(75,false),(71,false),(83,false),(91,false),(57,false)]
theorem der_52565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52565 :=
  CNF.rup_sound cl_52565 [cl_28582,cl_51348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28582 v h) (hints_cons _ _ _ (der_51348 v h) (by intro d hd; cases hd)))
def cl_52569 : CNF.NClause := [(57,false),(75,false),(71,false),(83,false),(91,false),(79,true)]
theorem der_52569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52569 :=
  CNF.rup_sound cl_52569 [cl_28592,cl_33807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28592 v h) (hints_cons _ _ _ (der_33807 v h) (by intro d hd; cases hd)))
def cl_52573 : CNF.NClause := [(83,true),(75,false),(71,false),(91,false),(62,false),(57,false)]
theorem der_52573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52573 :=
  CNF.rup_sound cl_52573 [cl_28605,cl_33876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28605 v h) (hints_cons _ _ _ (der_33876 v h) (by intro d hd; cases hd)))
def cl_52576 : CNF.NClause := [(57,false),(26,false),(83,false),(62,false),(75,true),(79,false)]
theorem der_52576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52576 :=
  CNF.rup_sound cl_52576 [cl_28638,cl_51343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28638 v h) (hints_cons _ _ _ (der_51343 v h) (by intro d hd; cases hd)))
def cl_52577 : CNF.NClause := [(57,false),(71,false),(83,false),(62,false),(79,true),(75,false)]
theorem der_52577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52577 :=
  CNF.rup_sound cl_52577 [cl_28645,cl_52063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28645 v h) (hints_cons _ _ _ (der_52063 v h) (by intro d hd; cases hd)))
def cl_52578 : CNF.NClause := [(91,true),(71,false),(83,true),(79,true),(26,true),(57,false)]
theorem der_52578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52578 :=
  CNF.rup_sound cl_52578 [cl_28681,cl_51368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28681 v h) (hints_cons _ _ _ (der_51368 v h) (by intro d hd; cases hd)))
def cl_52588 : CNF.NClause := [(70,true),(69,false),(51,false),(67,false),(68,false),(20,false)]
theorem der_52588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52588 :=
  CNF.rup_sound cl_52588 [cl_28728,cl_33973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28728 v h) (hints_cons _ _ _ (der_33973 v h) (by intro d hd; cases hd)))
def cl_52589 : CNF.NClause := [(92,true),(71,false),(51,false),(68,false),(20,false),(70,false)]
theorem der_52589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52589 :=
  CNF.rup_sound cl_52589 [cl_34956,cl_51402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34956 v h) (hints_cons _ _ _ (der_51402 v h) (by intro d hd; cases hd)))
def cl_52592 : CNF.NClause := [(68,true),(70,false),(69,false),(71,false),(51,false),(20,false)]
theorem der_52592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52592 :=
  CNF.rup_sound cl_52592 [cl_28747,cl_51400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28747 v h) (hints_cons _ _ _ (der_51400 v h) (by intro d hd; cases hd)))
def cl_52594 : CNF.NClause := [(70,false),(51,false),(69,true),(71,false),(68,false),(20,true)]
theorem der_52594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52594 :=
  CNF.rup_sound cl_52594 [cl_28754,cl_51378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28754 v h) (hints_cons _ _ _ (der_51378 v h) (by intro d hd; cases hd)))
def cl_52595 : CNF.NClause := [(70,true),(67,false),(69,false),(51,false),(71,false),(20,false)]
theorem der_52595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52595 :=
  CNF.rup_sound cl_52595 [cl_28759,cl_33942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28759 v h) (hints_cons _ _ _ (der_33942 v h) (by intro d hd; cases hd)))
def cl_52596 : CNF.NClause := [(51,false),(69,false),(71,true),(68,false),(70,false),(20,false)]
theorem der_52596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52596 :=
  CNF.rup_sound cl_52596 [cl_28775,cl_51405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28775 v h) (hints_cons _ _ _ (der_51405 v h) (by intro d hd; cases hd)))
def cl_52599 : CNF.NClause := [(90,false),(85,false),(50,false),(77,false),(71,false),(74,true)]
theorem der_52599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52599 :=
  CNF.rup_sound cl_52599 [cl_28812,cl_49560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28812 v h) (hints_cons _ _ _ (der_49560 v h) (by intro d hd; cases hd)))
def cl_52601 : CNF.NClause := [(85,false),(74,false),(50,false),(71,false),(63,true),(19,false)]
theorem der_52601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52601 :=
  CNF.rup_sound cl_52601 [cl_28818,cl_51445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28818 v h) (hints_cons _ _ _ (der_51445 v h) (by intro d hd; cases hd)))
def cl_52602 : CNF.NClause := [(63,false),(50,false),(71,true),(74,false),(90,false),(19,false)]
theorem der_52602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52602 :=
  CNF.rup_sound cl_52602 [cl_28820,cl_51457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28820 v h) (hints_cons _ _ _ (der_51457 v h) (by intro d hd; cases hd)))
def cl_52604 : CNF.NClause := [(85,true),(77,false),(71,false),(90,false),(50,false),(19,false)]
theorem der_52604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52604 :=
  CNF.rup_sound cl_52604 [cl_28832,cl_51421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28832 v h) (hints_cons _ _ _ (der_51421 v h) (by intro d hd; cases hd)))
def cl_52605 : CNF.NClause := [(85,true),(50,false),(74,false),(90,false),(63,false),(19,false)]
theorem der_52605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52605 :=
  CNF.rup_sound cl_52605 [cl_28845,cl_51457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28845 v h) (hints_cons _ _ _ (der_51457 v h) (by intro d hd; cases hd)))
def cl_52606 : CNF.NClause := [(50,false),(77,true),(90,false),(63,true),(74,false),(19,false)]
theorem der_52606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52606 :=
  CNF.rup_sound cl_52606 [cl_28847,cl_51427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28847 v h) (hints_cons _ _ _ (der_51427 v h) (by intro d hd; cases hd)))
def cl_52608 : CNF.NClause := [(63,false),(77,false),(50,false),(71,true),(74,false),(19,false)]
theorem der_52608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52608 :=
  CNF.rup_sound cl_52608 [cl_28863,cl_34049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28863 v h) (hints_cons _ _ _ (der_34049 v h) (by intro d hd; cases hd)))
def cl_52609 : CNF.NClause := [(90,true),(77,false),(85,false),(50,false),(74,true),(19,false)]
theorem der_52609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52609 :=
  CNF.rup_sound cl_52609 [cl_28870,cl_51445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28870 v h) (hints_cons _ _ _ (der_51445 v h) (by intro d hd; cases hd)))
def cl_52611 : CNF.NClause := [(85,true),(19,false),(63,false),(50,false),(77,false),(74,false)]
theorem der_52611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52611 :=
  CNF.rup_sound cl_52611 [cl_28887,cl_34049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28887 v h) (hints_cons _ _ _ (der_34049 v h) (by intro d hd; cases hd)))
def cl_52612 : CNF.NClause := [(50,false),(90,true),(74,true),(77,false),(63,true),(71,true)]
theorem der_52612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52612 :=
  CNF.rup_sound cl_52612 [cl_28901,cl_51437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28901 v h) (hints_cons _ _ _ (der_51437 v h) (by intro d hd; cases hd)))
def cl_52615 : CNF.NClause := [(87,false),(32,false),(81,false),(76,false),(86,false),(71,true)]
theorem der_52615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52615 :=
  CNF.rup_sound cl_52615 [cl_34958,cl_42905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34958 v h) (hints_cons _ _ _ (der_42905 v h) (by intro d hd; cases hd)))
def cl_52616 : CNF.NClause := [(87,false),(32,false),(76,false),(86,false),(81,false),(66,true)]
theorem der_52616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52616 :=
  CNF.rup_sound cl_52616 [cl_28920,cl_42905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28920 v h) (hints_cons _ _ _ (der_42905 v h) (by intro d hd; cases hd)))
def cl_52621 : CNF.NClause := [(32,false),(76,false),(86,false),(87,false),(81,true),(1,false)]
theorem der_52621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52621 :=
  CNF.rup_sound cl_52621 [cl_34960,cl_34081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34960 v h) (hints_cons _ _ _ (der_34081 v h) (by intro d hd; cases hd)))
def cl_52622 : CNF.NClause := [(32,false),(76,false),(71,false),(86,false),(87,false),(1,true)]
theorem der_52622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52622 :=
  CNF.rup_sound cl_52622 [cl_28929,cl_34080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28929 v h) (hints_cons _ _ _ (der_34080 v h) (by intro d hd; cases hd)))
def cl_52627 : CNF.NClause := [(87,false),(32,false),(71,false),(76,false),(86,true),(81,false)]
theorem der_52627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52627 :=
  CNF.rup_sound cl_52627 [cl_34961,cl_52078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34961 v h) (hints_cons _ _ _ (der_52078 v h) (by intro d hd; cases hd)))
def cl_52629 : CNF.NClause := [(87,false),(32,false),(81,false),(76,false),(71,true),(66,false)]
theorem der_52629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52629 :=
  CNF.rup_sound cl_52629 [cl_28947,cl_52078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28947 v h) (hints_cons _ _ _ (der_52078 v h) (by intro d hd; cases hd)))
def cl_52632 : CNF.NClause := [(76,true),(32,false),(81,false),(71,false),(86,true),(87,false)]
theorem der_52632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52632 :=
  CNF.rup_sound cl_52632 [cl_28952,cl_51475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28952 v h) (hints_cons _ _ _ (der_51475 v h) (by intro d hd; cases hd)))
def cl_52633 : CNF.NClause := [(32,false),(76,false),(86,true),(71,false),(66,false),(81,true)]
theorem der_52633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52633 :=
  CNF.rup_sound cl_52633 [cl_28960,cl_34151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28960 v h) (hints_cons _ _ _ (der_34151 v h) (by intro d hd; cases hd)))
def cl_52634 : CNF.NClause := [(32,false),(76,false),(86,false),(66,false),(1,false),(87,true)]
theorem der_52634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52634 :=
  CNF.rup_sound cl_52634 [cl_28978,cl_51494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28978 v h) (hints_cons _ _ _ (der_51494 v h) (by intro d hd; cases hd)))
def cl_52636 : CNF.NClause := [(32,false),(86,false),(71,false),(81,false),(1,false),(87,true)]
theorem der_52636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52636 :=
  CNF.rup_sound cl_52636 [cl_28984,cl_52104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28984 v h) (hints_cons _ _ _ (der_52104 v h) (by intro d hd; cases hd)))
def cl_52637 : CNF.NClause := [(87,true),(32,false),(76,false),(66,false),(81,true),(71,false)]
theorem der_52637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52637 :=
  CNF.rup_sound cl_52637 [cl_28991,cl_34151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28991 v h) (hints_cons _ _ _ (der_34151 v h) (by intro d hd; cases hd)))
def cl_52638 : CNF.NClause := [(32,false),(71,false),(76,false),(66,false),(1,false),(87,true)]
theorem der_52638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52638 :=
  CNF.rup_sound cl_52638 [cl_29006,cl_51494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29006 v h) (hints_cons _ _ _ (der_51494 v h) (by intro d hd; cases hd)))
def cl_52639 : CNF.NClause := [(32,false),(71,true),(76,false),(86,true),(66,false),(1,false)]
theorem der_52639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52639 :=
  CNF.rup_sound cl_52639 [cl_29010,cl_51494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29010 v h) (hints_cons _ _ _ (der_51494 v h) (by intro d hd; cases hd)))
def cl_52640 : CNF.NClause := [(32,false),(76,false),(71,false),(86,true),(81,true),(87,true)]
theorem der_52640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52640 :=
  CNF.rup_sound cl_52640 [cl_29025,cl_51493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29025 v h) (hints_cons _ _ _ (der_51493 v h) (by intro d hd; cases hd)))
def cl_52642 : CNF.NClause := [(65,false),(91,false),(69,false),(86,true),(73,false),(49,false)]
theorem der_52642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52642 :=
  CNF.rup_sound cl_52642 [cl_34962,cl_49717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34962 v h) (hints_cons _ _ _ (der_49717 v h) (by intro d hd; cases hd)))
def cl_52643 : CNF.NClause := [(91,true),(65,false),(69,false),(73,false),(18,false),(49,false)]
theorem der_52643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52643 :=
  CNF.rup_sound cl_52643 [cl_29041,cl_51843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29041 v h) (hints_cons _ _ _ (der_51843 v h) (by intro d hd; cases hd)))
def cl_52647 : CNF.NClause := [(88,false),(71,false),(44,false),(78,false),(84,true),(65,false)]
theorem der_52647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52647 :=
  CNF.rup_sound cl_52647 [cl_29058,cl_47225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29058 v h) (hints_cons _ _ _ (der_47225 v h) (by intro d hd; cases hd)))
def cl_52649 : CNF.NClause := [(67,false),(88,false),(73,false),(52,false),(85,true),(21,false)]
theorem der_52649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52649 :=
  CNF.rup_sound cl_52649 [cl_29067,cl_51655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29067 v h) (hints_cons _ _ _ (der_51655 v h) (by intro d hd; cases hd)))
def cl_52650 : CNF.NClause := [(67,false),(73,false),(52,false),(66,false),(79,true),(21,false)]
theorem der_52650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52650 :=
  CNF.rup_sound cl_52650 [cl_29068,cl_34305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29068 v h) (hints_cons _ _ _ (der_34305 v h) (by intro d hd; cases hd)))
def cl_52652 : CNF.NClause := [(79,true),(86,false),(63,false),(70,false),(72,false),(45,false)]
theorem der_52652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52652 :=
  CNF.rup_sound cl_52652 [cl_29071,cl_49540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29071 v h) (hints_cons _ _ _ (der_49540 v h) (by intro d hd; cases hd)))
def cl_52653 : CNF.NClause := [(89,false),(86,false),(14,true),(45,false),(72,false),(79,true)]
theorem der_52653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52653 :=
  CNF.rup_sound cl_52653 [cl_34963,cl_51888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34963 v h) (hints_cons _ _ _ (der_51888 v h) (by intro d hd; cases hd)))
def cl_52658 : CNF.NClause := [(68,true),(66,false),(75,false),(84,false),(89,false),(47,false)]
theorem der_52658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52658 :=
  CNF.rup_sound cl_52658 [cl_29126,cl_52210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29126 v h) (hints_cons _ _ _ (der_52210 v h) (by intro d hd; cases hd)))
def cl_52660 : CNF.NClause := [(77,true),(84,false),(16,false),(89,false),(68,false),(47,false)]
theorem der_52660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52660 :=
  CNF.rup_sound cl_52660 [cl_29161,cl_34653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29161 v h) (hints_cons _ _ _ (der_34653 v h) (by intro d hd; cases hd)))
def cl_52662 : CNF.NClause := [(77,false),(75,true),(89,false),(47,false),(84,true),(66,true)]
theorem der_52662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52662 :=
  CNF.rup_sound cl_52662 [cl_29168,cl_49547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29168 v h) (hints_cons _ _ _ (der_49547 v h) (by intro d hd; cases hd)))
def cl_52663 : CNF.NClause := [(77,false),(47,false),(16,false),(68,false),(66,true),(75,false)]
theorem der_52663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52663 :=
  CNF.rup_sound cl_52663 [cl_29173,cl_34399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29173 v h) (hints_cons _ _ _ (der_34399 v h) (by intro d hd; cases hd)))
def cl_52666 : CNF.NClause := [(85,true),(88,false),(52,false),(79,false),(67,false),(21,false)]
theorem der_52666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52666 :=
  CNF.rup_sound cl_52666 [cl_29192,cl_51767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29192 v h) (hints_cons _ _ _ (der_51767 v h) (by intro d hd; cases hd)))
def cl_52670 : CNF.NClause := [(67,false),(66,true),(85,false),(21,true),(52,false),(88,true)]
theorem der_52670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52670 :=
  CNF.rup_sound cl_52670 [cl_29232,cl_51857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29232 v h) (hints_cons _ _ _ (der_51857 v h) (by intro d hd; cases hd)))
def cl_52671 : CNF.NClause := [(79,false),(52,false),(88,true),(67,false),(66,true),(21,true)]
theorem der_52671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52671 :=
  CNF.rup_sound cl_52671 [cl_29236,cl_51659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29236 v h) (hints_cons _ _ _ (der_51659 v h) (by intro d hd; cases hd)))
def cl_52676 : CNF.NClause := [(78,true),(71,false),(13,true),(44,false),(84,true),(88,true)]
theorem der_52676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52676 :=
  CNF.rup_sound cl_52676 [cl_29274,cl_51836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29274 v h) (hints_cons _ _ _ (der_51836 v h) (by intro d hd; cases hd)))
def cl_52680 : CNF.NClause := [(73,false),(91,false),(69,false),(86,true),(49,false),(18,false)]
theorem der_52680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52680 :=
  CNF.rup_sound cl_52680 [cl_29283,cl_51718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29283 v h) (hints_cons _ _ _ (der_51718 v h) (by intro d hd; cases hd)))
def cl_52685 : CNF.NClause := [(88,false),(84,false),(44,false),(78,false),(71,false),(65,true)]
theorem der_52685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52685 :=
  CNF.rup_sound cl_52685 [cl_29307,cl_34504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29307 v h) (hints_cons _ _ _ (der_34504 v h) (by intro d hd; cases hd)))
def cl_52686 : CNF.NClause := [(73,true),(91,false),(49,false),(77,false),(86,false),(18,false)]
theorem der_52686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52686 :=
  CNF.rup_sound cl_52686 [cl_29371,cl_51838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29371 v h) (hints_cons _ _ _ (der_51838 v h) (by intro d hd; cases hd)))
def cl_52688 : CNF.NClause := [(67,false),(79,false),(85,false),(73,true),(52,false),(21,false)]
theorem der_52688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52688 :=
  CNF.rup_sound cl_52688 [cl_29379,cl_51769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29379 v h) (hints_cons _ _ _ (der_51769 v h) (by intro d hd; cases hd)))
def cl_52689 : CNF.NClause := [(89,true),(72,false),(63,false),(70,false),(45,false),(79,false)]
theorem der_52689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52689 :=
  CNF.rup_sound cl_52689 [cl_29403,cl_49540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29403 v h) (hints_cons _ _ _ (der_49540 v h) (by intro d hd; cases hd)))
def cl_52691 : CNF.NClause := [(65,false),(72,false),(88,true),(44,false),(13,false),(71,false)]
theorem der_52691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52691 :=
  CNF.rup_sound cl_52691 [cl_29441,cl_51826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29441 v h) (hints_cons _ _ _ (der_51826 v h) (by intro d hd; cases hd)))
def cl_52693 : CNF.NClause := [(77,false),(84,false),(89,false),(66,false),(47,false),(75,true)]
theorem der_52693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52693 :=
  CNF.rup_sound cl_52693 [cl_29460,cl_49547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29460 v h) (hints_cons _ _ _ (der_49547 v h) (by intro d hd; cases hd)))
def cl_52696 : CNF.NClause := [(79,true),(86,false),(89,false),(70,false),(45,false),(63,false)]
theorem der_52696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52696 :=
  CNF.rup_sound cl_52696 [cl_29485,cl_51827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29485 v h) (hints_cons _ _ _ (der_51827 v h) (by intro d hd; cases hd)))
def cl_52697 : CNF.NClause := [(70,false),(45,false),(63,false),(89,false),(86,true),(79,false)]
theorem der_52697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52697 :=
  CNF.rup_sound cl_52697 [cl_29486,cl_47228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29486 v h) (hints_cons _ _ _ (der_47228 v h) (by intro d hd; cases hd)))
def cl_52700 : CNF.NClause := [(88,false),(78,true),(44,false),(84,false),(71,false),(13,false)]
theorem der_52700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52700 :=
  CNF.rup_sound cl_52700 [cl_29497,cl_51694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29497 v h) (hints_cons _ _ _ (der_51694 v h) (by intro d hd; cases hd)))
def cl_52701 : CNF.NClause := [(91,false),(18,false),(49,false),(69,true),(77,false),(73,false)]
theorem der_52701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52701 :=
  CNF.rup_sound cl_52701 [cl_29520,cl_34702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29520 v h) (hints_cons _ _ _ (der_34702 v h) (by intro d hd; cases hd)))
def cl_52702 : CNF.NClause := [(65,false),(73,false),(49,false),(77,false),(18,false),(91,true)]
theorem der_52702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52702 :=
  CNF.rup_sound cl_52702 [cl_29528,cl_51850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29528 v h) (hints_cons _ _ _ (der_51850 v h) (by intro d hd; cases hd)))
def cl_52703 : CNF.NClause := [(67,true),(90,false),(75,false),(53,false),(78,false),(86,false)]
theorem der_52703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52703 :=
  CNF.rup_sound cl_52703 [cl_34966,cl_34842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34966 v h) (hints_cons _ _ _ (der_34842 v h) (by intro d hd; cases hd)))
def cl_52706 : CNF.NClause := [(75,false),(64,false),(53,false),(78,false),(86,true),(22,false)]
theorem der_52706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52706 :=
  CNF.rup_sound cl_52706 [cl_29571,cl_51880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29571 v h) (hints_cons _ _ _ (der_51880 v h) (by intro d hd; cases hd)))
def cl_52707 : CNF.NClause := [(75,false),(86,false),(53,false),(78,false),(64,false),(90,true)]
theorem der_52707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52707 :=
  CNF.rup_sound cl_52707 [cl_29575,cl_34789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29575 v h) (hints_cons _ _ _ (der_34789 v h) (by intro d hd; cases hd)))
def cl_52709 : CNF.NClause := [(90,false),(22,true),(53,false),(78,false),(86,false),(75,true)]
theorem der_52709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52709 :=
  CNF.rup_sound cl_52709 [cl_29599,cl_34782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29599 v h) (hints_cons _ _ _ (der_34782 v h) (by intro d hd; cases hd)))
def cl_52711 : CNF.NClause := [(75,false),(86,false),(22,true),(53,false),(78,false),(64,false)]
theorem der_52711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52711 :=
  CNF.rup_sound cl_52711 [cl_29614,cl_34789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29614 v h) (hints_cons _ _ _ (der_34789 v h) (by intro d hd; cases hd)))
def cl_52713 : CNF.NClause := [(86,false),(63,true),(72,true),(89,false),(45,false),(79,false)]
theorem der_52713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52713 :=
  CNF.rup_sound cl_52713 [cl_29631,cl_51884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29631 v h) (hints_cons _ _ _ (der_51884 v h) (by intro d hd; cases hd)))
def cl_52714 : CNF.NClause := [(86,false),(45,false),(89,false),(70,false),(63,true),(72,true)]
theorem der_52714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52714 :=
  CNF.rup_sound cl_52714 [cl_29635,cl_51828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29635 v h) (hints_cons _ _ _ (der_51828 v h) (by intro d hd; cases hd)))
def cl_52715 : CNF.NClause := [(89,false),(70,false),(45,false),(79,false),(63,true),(72,true)]
theorem der_52715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52715 :=
  CNF.rup_sound cl_52715 [cl_29639,cl_52070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29639 v h) (hints_cons _ _ _ (der_52070 v h) (by intro d hd; cases hd)))
def cl_52716 : CNF.NClause := [(89,true),(86,false),(72,false),(45,false),(79,false),(14,false)]
theorem der_52716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52716 :=
  CNF.rup_sound cl_52716 [cl_29645,cl_51891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29645 v h) (hints_cons _ _ _ (der_51891 v h) (by intro d hd; cases hd)))
def cl_52717 : CNF.NClause := [(75,false),(64,true),(86,false),(67,false),(53,false),(22,false)]
theorem der_52717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52717 :=
  CNF.rup_sound cl_52717 [cl_34969,cl_51964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34969 v h) (hints_cons _ _ _ (der_51964 v h) (by intro d hd; cases hd)))
def cl_52720 : CNF.NClause := [(75,true),(65,false),(87,false),(34,false),(80,false),(85,false)]
theorem der_52720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52720 :=
  CNF.rup_sound cl_52720 [cl_35255,cl_52399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35255 v h) (hints_cons _ _ _ (der_52399 v h) (by intro d hd; cases hd)))
def cl_52722 : CNF.NClause := [(65,false),(67,false),(81,false),(23,true),(83,false),(54,false)]
theorem der_52722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52722 :=
  CNF.rup_sound cl_52722 [cl_35069,cl_32538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35069 v h) (hints_cons _ _ _ (der_32538 v h) (by intro d hd; cases hd)))
def cl_52723 : CNF.NClause := [(76,true),(80,true),(55,false),(67,false),(63,false),(84,false)]
theorem der_52723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52723 :=
  CNF.rup_sound cl_52723 [cl_35608,cl_50896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35608 v h) (hints_cons _ _ _ (der_50896 v h) (by intro d hd; cases hd)))
def cl_52724 : CNF.NClause := [(73,false),(65,false),(18,true),(49,false),(69,false),(77,false)]
theorem der_52724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52724 :=
  CNF.rup_sound cl_52724 [cl_35149,cl_49713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35149 v h) (hints_cons _ _ _ (der_49713 v h) (by intro d hd; cases hd)))
def cl_52725 : CNF.NClause := [(46,false),(79,false),(15,true),(80,false),(81,false),(78,false)]
theorem der_52725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52725 :=
  CNF.rup_sound cl_52725 [cl_35599,cl_50913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35599 v h) (hints_cons _ _ _ (der_50913 v h) (by intro d hd; cases hd)))
def cl_52730 : CNF.NClause := [(3,true),(65,false),(34,false),(87,false),(70,false),(80,false)]
theorem der_52730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52730 :=
  CNF.rup_sound cl_52730 [cl_36243,cl_52043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36243 v h) (hints_cons _ _ _ (der_52043 v h) (by intro d hd; cases hd)))
def cl_52731 : CNF.NClause := [(67,false),(23,true),(81,false),(74,false),(65,true),(54,false)]
theorem der_52731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52731 :=
  CNF.rup_sound cl_52731 [cl_35992,cl_50800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35992 v h) (hints_cons _ _ _ (der_50800 v h) (by intro d hd; cases hd)))
def cl_52733 : CNF.NClause := [(64,false),(82,true),(38,false),(73,false),(80,false),(71,false)]
theorem der_52733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52733 :=
  CNF.rup_sound cl_52733 [cl_41601,cl_52500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41601 v h) (hints_cons _ _ _ (der_52500 v h) (by intro d hd; cases hd)))
def cl_52734 : CNF.NClause := [(89,false),(64,false),(38,false),(7,true),(73,false),(80,false)]
theorem der_52734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52734 :=
  CNF.rup_sound cl_52734 [cl_42906,cl_51133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42906 v h) (hints_cons _ _ _ (der_51133 v h) (by intro d hd; cases hd)))
def cl_52736 : CNF.NClause := [(70,false),(37,false),(82,true),(6,true),(78,true),(74,false)]
theorem der_52736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52736 :=
  CNF.rup_sound cl_52736 [cl_41943,cl_50549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41943 v h) (hints_cons _ _ _ (der_50549 v h) (by intro d hd; cases hd)))
def cl_52741 : CNF.NClause := [(126,true),(152,true),(13,true),(5,true),(148,false),(84,true)]
theorem der_52741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52741 :=
  CNF.rup_sound cl_52741 [cl_45948,cl_15771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45948 v h) (hints_cons _ _ _ (der_15771 v h) (by intro d hd; cases hd)))
def cl_52743 : CNF.NClause := [(65,false),(79,true),(39,false),(76,false),(68,false),(8,true)]
theorem der_52743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52743 :=
  CNF.rup_sound cl_52743 [cl_45486,cl_32153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45486 v h) (hints_cons _ _ _ (der_32153 v h) (by intro d hd; cases hd)))
def cl_52749 : CNF.NClause := [(77,true),(16,false),(138,true),(137,true),(145,true),(148,true),(153,true),(128,true)]
theorem der_52749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52749 :=
  CNF.rup_sound cl_52749 [cl_35679,cl_29850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35679 v h) (hints_cons _ _ _ (der_29850 v h) (by intro d hd; cases hd)))
def cl_52752 : CNF.NClause := [(16,false),(89,false),(75,false),(68,false),(47,true),(66,false),(18,false),(84,false)]
theorem der_52752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52752 :=
  CNF.rup_sound cl_52752 [cl_38009,cl_42209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38009 v h) (hints_cons _ _ _ (der_42209 v h) (by intro d hd; cases hd)))
def cl_52753 : CNF.NClause := [(67,true),(22,false),(1081,true),(1057,true),(1069,true),(1066,true),(1064,true),(1073,false)]
theorem der_52753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52753 :=
  CNF.rup_sound cl_52753 [cl_36879,cl_35629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36879 v h) (hints_cons _ _ _ (der_35629 v h) (by intro d hd; cases hd)))
def cl_52754 : CNF.NClause := [(67,true),(1072,true),(1068,false),(1069,true),(1064,true),(23,false),(1083,true),(1055,true)]
theorem der_52754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52754 :=
  CNF.rup_sound cl_52754 [cl_36805,cl_49785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36805 v h) (hints_cons _ _ _ (der_49785 v h) (by intro d hd; cases hd)))
def cl_52755 : CNF.NClause := [(88,true),(134,true),(128,false),(142,true),(150,true),(151,true),(9,false),(131,true)]
theorem der_52755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52755 :=
  CNF.rup_sound cl_52755 [cl_36507,cl_49835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36507 v h) (hints_cons _ _ _ (der_49835 v h) (by intro d hd; cases hd)))
def cl_52758 : CNF.NClause := [(85,false),(23,false),(76,false),(58,true),(69,false),(7,true),(78,false),(151,false)]
theorem der_52758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52758 :=
  CNF.rup_sound cl_52758 [cl_39645,cl_42018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39645 v h) (hints_cons _ _ _ (der_42018 v h) (by intro d hd; cases hd)))
def cl_52759 : CNF.NClause := [(76,false),(8,false),(9,false),(65,false),(79,false),(39,true),(68,false),(90,false)]
theorem der_52759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52759 :=
  CNF.rup_sound cl_52759 [cl_43001,cl_43194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43001 v h) (hints_cons _ _ _ (der_43194 v h) (by intro d hd; cases hd)))
def cl_52760 : CNF.NClause := [(80,false),(19,false),(46,true),(81,false),(79,false),(92,false),(15,false),(78,false)]
theorem der_52760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52760 :=
  CNF.rup_sound cl_52760 [cl_41959,cl_38014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41959 v h) (hints_cons _ _ _ (der_38014 v h) (by intro d hd; cases hd)))
def cl_52762 : CNF.NClause := [(26,false),(27,false),(18,false),(79,false),(75,false),(83,false),(57,true),(71,false)]
theorem der_52762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52762 :=
  CNF.rup_sound cl_52762 [cl_40931,cl_48149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40931 v h) (hints_cons _ _ _ (der_48149 v h) (by intro d hd; cases hd)))
def cl_52763 : CNF.NClause := [(69,false),(17,false),(24,false),(18,false),(65,false),(73,false),(49,true),(86,false)]
theorem der_52763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52763 :=
  CNF.rup_sound cl_52763 [cl_42341,cl_47750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42341 v h) (hints_cons _ _ _ (der_47750 v h) (by intro d hd; cases hd)))
def cl_52764 : CNF.NClause := [(36,true),(3,false),(5,false),(92,false),(83,false),(86,false),(82,false),(28,false)]
theorem der_52764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52764 :=
  CNF.rup_sound cl_52764 [cl_42504,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42504 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_52765 : CNF.NClause := [(83,false),(12,false),(27,false),(26,false),(79,false),(75,false),(20,false),(57,true)]
theorem der_52765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52765 :=
  CNF.rup_sound cl_52765 [cl_44989,cl_44921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44989 v h) (hints_cons _ _ _ (der_44921 v h) (by intro d hd; cases hd)))
def cl_52772 : CNF.NClause := [(85,false),(43,true),(12,false),(10,false),(81,false),(64,false),(6,false),(68,false)]
theorem der_52772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52772 :=
  CNF.rup_sound cl_52772 [cl_47833,cl_47704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47833 v h) (hints_cons _ _ _ (der_47704 v h) (by intro d hd; cases hd)))
def cl_52775 : CNF.NClause := [(136,true),(14,false),(89,true),(142,true),(132,true),(135,true),(127,true),(134,true)]
theorem der_52775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52775 :=
  CNF.rup_sound cl_52775 [cl_49260,cl_37439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49260 v h) (hints_cons _ _ _ (der_37439 v h) (by intro d hd; cases hd)))
def cl_52777 : CNF.NClause := [(65,false),(76,false),(8,false),(79,false),(39,true),(7,false),(68,false),(90,false)]
theorem der_52777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52777 :=
  CNF.rup_sound cl_52777 [cl_49447,cl_52759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49447 v h) (hints_cons _ _ _ (der_52759 v h) (by intro d hd; cases hd)))
def cl_52778 : CNF.NClause := [(151,true),(77,true),(138,true),(137,true),(139,true),(16,false),(131,true),(132,true),(127,true)]
theorem der_52778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52778 :=
  CNF.rup_sound cl_52778 [cl_35692,cl_49799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35692 v h) (hints_cons _ _ _ (der_49799 v h) (by intro d hd; cases hd)))
def cl_52779 : CNF.NClause := [(130,false),(77,true),(16,false),(137,true),(132,true),(153,true),(127,true),(134,true),(126,true)]
theorem der_52779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52779 :=
  CNF.rup_sound cl_52779 [cl_35607,cl_49799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35607 v h) (hints_cons _ _ _ (der_49799 v h) (by intro d hd; cases hd)))
def cl_52780 : CNF.NClause := [(127,true),(77,true),(138,true),(139,true),(151,true),(131,true),(132,true),(16,false),(147,true)]
theorem der_52780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52780 :=
  CNF.rup_sound cl_52780 [cl_35826,cl_49799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35826 v h) (hints_cons _ _ _ (der_49799 v h) (by intro d hd; cases hd)))
def cl_52781 : CNF.NClause := [(91,true),(922,true),(909,true),(911,true),(926,true),(901,true),(918,true),(6,false),(927,true)]
theorem der_52781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52781 :=
  CNF.rup_sound cl_52781 [cl_35206,cl_42457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35206 v h) (hints_cons _ _ _ (der_42457 v h) (by intro d hd; cases hd)))
def cl_52782 : CNF.NClause := [(7,true),(26,false),(19,false),(28,false),(79,false),(75,false),(83,false),(57,true),(91,false)]
theorem der_52782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52782 :=
  CNF.rup_sound cl_52782 [cl_35986,cl_39382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35986 v h) (hints_cons _ _ _ (der_39382 v h) (by intro d hd; cases hd)))
def cl_52783 : CNF.NClause := [(77,true),(922,true),(911,true),(906,true),(913,true),(17,false),(902,true),(904,true),(920,false)]
theorem der_52783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52783 :=
  CNF.rup_sound cl_52783 [cl_36092,cl_49875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36092 v h) (hints_cons _ _ _ (der_49875 v h) (by intro d hd; cases hd)))
def cl_52784 : CNF.NClause := [(142,true),(77,true),(138,true),(137,true),(145,true),(17,false),(148,true),(153,true),(128,true)]
theorem der_52784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52784 :=
  CNF.rup_sound cl_52784 [cl_36803,cl_49875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36803 v h) (hints_cons _ _ _ (der_49875 v h) (by intro d hd; cases hd)))
def cl_52789 : CNF.NClause := [(26,false),(80,false),(29,false),(17,false),(13,true),(68,false),(74,false),(86,false),(60,true)]
theorem der_52789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52789 :=
  CNF.rup_sound cl_52789 [cl_39272,cl_40664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39272 v h) (hints_cons _ _ _ (der_40664 v h) (by intro d hd; cases hd)))
def cl_52792 : CNF.NClause := [(15,true),(19,false),(18,false),(74,false),(85,false),(63,false),(90,false),(71,false),(50,true)]
theorem der_52792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52792 :=
  CNF.rup_sound cl_52792 [cl_38492,cl_41733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38492 v h) (hints_cons _ _ _ (der_41733 v h) (by intro d hd; cases hd)))
def cl_52794 : CNF.NClause := [(7,true),(1,false),(71,true),(13,true),(1057,true),(1056,true),(1078,true),(1063,true),(1068,true)]
theorem der_52794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52794 :=
  CNF.rup_sound cl_52794 [cl_38826,cl_42582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38826 v h) (hints_cons _ _ _ (der_42582 v h) (by intro d hd; cases hd)))
def cl_52796 : CNF.NClause := [(55,true),(63,false),(24,false),(12,true),(76,false),(80,false),(6,false),(22,false),(84,false)]
theorem der_52796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52796 :=
  CNF.rup_sound cl_52796 [cl_39333,cl_40226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39333 v h) (hints_cons _ _ _ (der_40226 v h) (by intro d hd; cases hd)))
def cl_52797 : CNF.NClause := [(908,true),(91,true),(12,true),(24,false),(903,true),(913,true),(914,true),(916,true),(915,true)]
theorem der_52797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52797 :=
  CNF.rup_sound cl_52797 [cl_39389,cl_49793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39389 v h) (hints_cons _ _ _ (der_49793 v h) (by intro d hd; cases hd)))
def cl_52799 : CNF.NClause := [(65,false),(9,true),(21,false),(13,false),(72,false),(78,false),(84,false),(71,false),(44,true)]
theorem der_52799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52799 :=
  CNF.rup_sound cl_52799 [cl_42310,cl_39538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42310 v h) (hints_cons _ _ _ (der_39538 v h) (by intro d hd; cases hd)))
def cl_52800 : CNF.NClause := [(36,true),(28,false),(14,true),(5,false),(3,false),(92,false),(83,false),(82,false),(22,false)]
theorem der_52800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52800 :=
  CNF.rup_sound cl_52800 [cl_42631,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42631 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_52803 : CNF.NClause := [(18,false),(29,false),(14,true),(65,false),(73,false),(69,false),(49,true),(77,false),(91,false)]
theorem der_52803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52803 :=
  CNF.rup_sound cl_52803 [cl_43470,cl_45146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43470 v h) (hints_cons _ _ _ (der_45146 v h) (by intro d hd; cases hd)))
def cl_52812 : CNF.NClause := [(8,false),(22,true),(28,false),(9,false),(65,false),(76,false),(79,false),(39,true),(68,false)]
theorem der_52812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52812 :=
  CNF.rup_sound cl_52812 [cl_44428,cl_43940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44428 v h) (hints_cons _ _ _ (der_43940 v h) (by intro d hd; cases hd)))
def cl_52816 : CNF.NClause := [(79,false),(12,true),(26,false),(24,false),(75,false),(83,false),(57,true),(71,false),(62,false)]
theorem der_52816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52816 :=
  CNF.rup_sound cl_52816 [cl_44682,cl_42637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44682 v h) (hints_cons _ _ _ (der_42637 v h) (by intro d hd; cases hd)))
def cl_52817 : CNF.NClause := [(909,false),(41,true),(76,false),(92,false),(75,false),(74,false),(73,false),(912,true),(913,true)]
theorem der_52817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52817 :=
  CNF.rup_sound cl_52817 [cl_45185,cl_15876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45185 v h) (hints_cons _ _ _ (der_15876 v h) (by intro d hd; cases hd)))
def cl_52819 : CNF.NClause := [(36,true),(24,false),(3,false),(92,false),(85,false),(83,false),(86,false),(82,false),(5,false)]
theorem der_52819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52819 :=
  CNF.rup_sound cl_52819 [cl_44561,cl_52764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44561 v h) (hints_cons _ _ _ (der_52764 v h) (by intro d hd; cases hd)))
def cl_52820 : CNF.NClause := [(36,true),(13,false),(3,false),(92,false),(85,false),(83,false),(86,false),(82,false),(5,false)]
theorem der_52820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52820 :=
  CNF.rup_sound cl_52820 [cl_46562,cl_52764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46562 v h) (hints_cons _ _ _ (der_52764 v h) (by intro d hd; cases hd)))
def cl_52821 : CNF.NClause := [(69,false),(33,true),(15,false),(87,false),(17,false),(21,true),(2,false),(74,false),(84,false)]
theorem der_52821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52821 :=
  CNF.rup_sound cl_52821 [cl_45012,cl_49966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45012 v h) (hints_cons _ _ _ (der_49966 v h) (by intro d hd; cases hd)))
def cl_52822 : CNF.NClause := [(87,false),(33,true),(16,false),(13,true),(2,false),(79,false),(64,false),(74,false),(69,false)]
theorem der_52822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52822 :=
  CNF.rup_sound cl_52822 [cl_46046,cl_43853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46046 v h) (hints_cons _ _ _ (der_43853 v h) (by intro d hd; cases hd)))
def cl_52823 : CNF.NClause := [(9,true),(17,false),(11,false),(21,false),(79,false),(73,false),(52,true),(85,false),(67,false)]
theorem der_52823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52823 :=
  CNF.rup_sound cl_52823 [cl_45731,cl_43935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45731 v h) (hints_cons _ _ _ (der_43935 v h) (by intro d hd; cases hd)))
def cl_52824 : CNF.NClause := [(151,true),(11,false),(66,true),(133,true),(137,true),(132,true),(148,true),(153,true),(134,true)]
theorem der_52824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52824 :=
  CNF.rup_sound cl_52824 [cl_46001,cl_49878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46001 v h) (hints_cons _ _ _ (der_49878 v h) (by intro d hd; cases hd)))
def cl_52828 : CNF.NClause := [(17,false),(9,true),(16,false),(21,false),(79,false),(73,false),(52,true),(85,false),(67,false)]
theorem der_52828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52828 :=
  CNF.rup_sound cl_52828 [cl_44177,cl_43935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44177 v h) (hints_cons _ _ _ (der_43935 v h) (by intro d hd; cases hd)))
def cl_52829 : CNF.NClause := [(92,false),(16,false),(5,false),(28,true),(3,false),(83,false),(86,false),(82,false),(36,true)]
theorem der_52829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52829 :=
  CNF.rup_sound cl_52829 [cl_46544,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46544 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_52830 : CNF.NClause := [(92,false),(28,true),(3,false),(5,false),(83,false),(86,false),(82,false),(36,true),(1059,false)]
theorem der_52830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52830 :=
  CNF.rup_sound cl_52830 [cl_48062,cl_42433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48062 v h) (hints_cons _ _ _ (der_42433 v h) (by intro d hd; cases hd)))
def cl_52834 : CNF.NClause := [(1062,true),(8,false),(65,false),(76,false),(79,false),(39,true),(68,false),(90,false),(1063,true)]
theorem der_52834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52834 :=
  CNF.rup_sound cl_52834 [cl_48605,cl_52777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48605 v h) (hints_cons _ _ _ (der_52777 v h) (by intro d hd; cases hd)))
def cl_52837 : CNF.NClause := [(19,false),(8,false),(22,true),(65,false),(76,false),(79,false),(39,true),(6,false),(68,false)]
theorem der_52837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52837 :=
  CNF.rup_sound cl_52837 [cl_48916,cl_29851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48916 v h) (hints_cons _ _ _ (der_29851 v h) (by intro d hd; cases hd)))
def cl_52840 : CNF.NClause := [(73,false),(19,false),(12,true),(18,false),(65,false),(15,true),(6,false),(69,false),(49,true),(86,false)]
theorem der_52840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52840 :=
  CNF.rup_sound cl_52840 [cl_35662,cl_47750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35662 v h) (hints_cons _ _ _ (der_47750 v h) (by intro d hd; cases hd)))
def cl_52846 : CNF.NClause := [(67,true),(23,false),(903,false),(911,true),(907,true),(906,true),(921,true),(913,true),(926,true),(928,true)]
theorem der_52846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52846 :=
  CNF.rup_sound cl_52846 [cl_36208,cl_49785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36208 v h) (hints_cons _ _ _ (der_49785 v h) (by intro d hd; cases hd)))
def cl_52851 : CNF.NClause := [(70,true),(14,true),(6,false),(142,true),(150,true),(139,true),(143,true),(131,true),(153,true),(147,true)]
theorem der_52851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52851 :=
  CNF.rup_sound cl_52851 [cl_37543,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37543 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_52858 : CNF.NClause := [(23,true),(24,false),(21,false),(18,false),(76,false),(6,true),(80,false),(55,true),(63,false),(84,false)]
theorem der_52858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52858 :=
  CNF.rup_sound cl_52858 [cl_38038,cl_38013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38038 v h) (hints_cons _ _ _ (der_38013 v h) (by intro d hd; cases hd)))
def cl_52859 : CNF.NClause := [(23,false),(89,true),(7,true),(125,true),(128,false),(137,true),(145,true),(146,true),(139,true),(135,true)]
theorem der_52859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52859 :=
  CNF.rup_sound cl_52859 [cl_36263,cl_49783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36263 v h) (hints_cons _ _ _ (der_49783 v h) (by intro d hd; cases hd)))
def cl_52870 : CNF.NClause := [(3,true),(81,false),(6,true),(17,false),(28,false),(26,false),(73,false),(90,false),(84,false),(59,true)]
theorem der_52870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52870 :=
  CNF.rup_sound cl_52870 [cl_41732,cl_38519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41732 v h) (hints_cons _ _ _ (der_38519 v h) (by intro d hd; cases hd)))
def cl_52872 : CNF.NClause := [(1080,false),(27,false),(26,false),(79,false),(75,false),(83,false),(57,true),(71,false),(62,false),(1078,true)]
theorem der_52872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52872 :=
  CNF.rup_sound cl_52872 [cl_43616,cl_42637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43616 v h) (hints_cons _ _ _ (der_42637 v h) (by intro d hd; cases hd)))
def cl_52876 : CNF.NClause := [(65,false),(76,false),(7,true),(9,true),(79,false),(39,true),(68,false),(82,false),(90,false),(5,true)]
theorem der_52876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52876 :=
  CNF.rup_sound cl_52876 [cl_42654,cl_42907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42654 v h) (hints_cons _ _ _ (der_42907 v h) (by intro d hd; cases hd)))
def cl_52879 : CNF.NClause := [(585,true),(9,false),(29,false),(68,false),(74,false),(80,false),(86,false),(60,true),(14,true),(587,false)]
theorem der_52879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52879 :=
  CNF.rup_sound cl_52879 [cl_40955,cl_49837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40955 v h) (hints_cons _ _ _ (der_49837 v h) (by intro d hd; cases hd)))
def cl_52880 : CNF.NClause := [(148,false),(84,false),(76,false),(80,false),(55,true),(63,false),(24,false),(91,false),(22,true),(147,true)]
theorem der_52880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52880 :=
  CNF.rup_sound cl_52880 [cl_42070,cl_41548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42070 v h) (hints_cons _ _ _ (der_41548 v h) (by intro d hd; cases hd)))
def cl_52885 : CNF.NClause := [(146,true),(140,true),(130,true),(133,true),(14,false),(72,true),(131,true),(153,true),(126,true),(125,true)]
theorem der_52885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52885 :=
  CNF.rup_sound cl_52885 [cl_44184,cl_46317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44184 v h) (hints_cons _ _ _ (der_46317 v h) (by intro d hd; cases hd)))
def cl_52889 : CNF.NClause := [(80,false),(28,true),(42,true),(72,false),(69,false),(22,true),(83,false),(66,false),(90,false),(19,true)]
theorem der_52889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52889 :=
  CNF.rup_sound cl_52889 [cl_46757,cl_45805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46757 v h) (hints_cons _ _ _ (der_45805 v h) (by intro d hd; cases hd)))
def cl_52892 : CNF.NClause := [(21,false),(13,false),(28,true),(16,false),(15,false),(2,true),(89,false),(75,false),(68,false),(47,true)]
theorem der_52892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52892 :=
  CNF.rup_sound cl_52892 [cl_45241,cl_45606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45241 v h) (hints_cons _ _ _ (der_45606 v h) (by intro d hd; cases hd)))
def cl_52898 : CNF.NClause := [(17,false),(9,true),(21,false),(79,false),(73,false),(52,true),(85,false),(67,false),(135,true),(145,false)]
theorem der_52898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52898 :=
  CNF.rup_sound cl_52898 [cl_44908,cl_43935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44908 v h) (hints_cons _ _ _ (der_43935 v h) (by intro d hd; cases hd)))
def cl_52901 : CNF.NClause := [(60,false),(58,false),(36,false),(51,false),(33,true),(61,true),(46,false),(54,false),(96,false),(120,false)]
theorem der_52901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52901 :=
  CNF.rup_sound cl_52901 [cl_47487,cl_49523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47487 v h) (hints_cons _ _ _ (der_49523 v h) (by intro d hd; cases hd)))
def cl_52908 : CNF.NClause := [(91,true),(140,true),(146,true),(143,true),(151,true),(24,false),(131,true),(126,true),(137,false),(128,true)]
theorem der_52908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52908 :=
  CNF.rup_sound cl_52908 [cl_49367,cl_49776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49367 v h) (hints_cons _ _ _ (der_49776 v h) (by intro d hd; cases hd)))
def cl_52958 : CNF.NClause := [(1060,true),(1076,true),(72,true),(13,false),(10,true),(1062,true),(1072,true),(1082,true),(1058,true),(1080,true),(1063,false)]
theorem der_52958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52958 :=
  CNF.rup_sound cl_52958 [cl_45255,cl_46317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45255 v h) (hints_cons _ _ _ (der_46317 v h) (by intro d hd; cases hd)))
def cl_52970 : CNF.NClause := [(584,true),(14,true),(70,true),(17,true),(570,true),(579,true),(565,true),(580,true),(6,false),(581,true),(562,true),(568,true)]
theorem der_52970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52970 :=
  CNF.rup_sound cl_52970 [cl_35271,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35271 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_52974 : CNF.NClause := [(97,false),(95,false),(42,false),(43,false),(37,false),(46,true),(118,false),(110,false),(101,false),(113,false),(35,false),(33,false)]
theorem der_52974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52974 :=
  CNF.rup_sound cl_52974 [cl_37287,cl_50043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37287 v h) (hints_cons _ _ _ (der_50043 v h) (by intro d hd; cases hd)))
def cl_52991 : CNF.NClause := [(6,false),(14,true),(70,true),(1056,true),(1071,true),(1073,true),(1078,true),(1059,true),(1076,true),(1069,true),(1083,true),(1075,true)]
theorem der_52991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_52991 :=
  CNF.rup_sound cl_52991 [cl_40703,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40703 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_53006 : CNF.NClause := [(907,true),(901,true),(82,true),(912,true),(6,false),(911,true),(921,true),(925,true),(914,true),(918,true),(927,true),(915,true)]
theorem der_53006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53006 :=
  CNF.rup_sound cl_53006 [cl_43368,cl_42432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43368 v h) (hints_cons _ _ _ (der_42432 v h) (by intro d hd; cases hd)))
def cl_53033 : CNF.NClause := [(9,true),(12,false),(1,true),(81,true),(917,true),(903,true),(906,true),(926,true),(902,true),(918,true),(920,true),(919,true)]
theorem der_53033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53033 :=
  CNF.rup_sound cl_53033 [cl_48772,cl_51541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48772 v h) (hints_cons _ _ _ (der_51541 v h) (by intro d hd; cases hd)))
def cl_53078 : CNF.NClause := [(85,false),(22,false),(43,false),(65,false),(81,false),(68,false),(73,false),(69,false),(6,true),(49,true),(24,true),(77,false),(26,true)]
theorem der_53078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53078 :=
  CNF.rup_sound cl_53078 [cl_48353,cl_51051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48353 v h) (hints_cons _ _ _ (der_51051 v h) (by intro d hd; cases hd)))
def cl_53081 : CNF.NClause := [(733,true),(22,false),(90,true),(19,true),(715,true),(740,true),(714,true),(717,true),(720,true),(728,true),(731,true),(734,true),(739,true)]
theorem der_53081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53081 :=
  CNF.rup_sound cl_53081 [cl_48774,cl_49821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48774 v h) (hints_cons _ _ _ (der_49821 v h) (by intro d hd; cases hd)))
def cl_53084 : CNF.NClause := [(106,false),(115,false),(47,false),(55,false),(46,true),(48,true),(111,false),(120,false),(98,false),(107,false),(35,false),(40,false),(97,false),(122,false)]
theorem der_53084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53084 :=
  CNF.rup_sound cl_53084 [cl_35525,cl_50021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35525 v h) (hints_cons _ _ _ (der_50021 v h) (by intro d hd; cases hd)))
def cl_53085 : CNF.NClause := [(20,true),(76,false),(23,true),(64,false),(75,false),(21,true),(80,false),(78,false),(55,true),(86,false),(63,false),(53,false),(84,false),(91,false)]
theorem der_53085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53085 :=
  CNF.rup_sound cl_53085 [cl_37503,cl_52707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37503 v h) (hints_cons _ _ _ (der_52707 v h) (by intro d hd; cases hd)))
def cl_53103 : CNF.NClause := [(91,true),(1063,true),(1067,true),(1071,true),(1073,true),(6,false),(1076,true),(1061,true),(1064,true),(1083,true),(1082,true),(1055,true),(1058,true),(1081,false)]
theorem der_53103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53103 :=
  CNF.rup_sound cl_53103 [cl_46523,cl_42457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46523 v h) (hints_cons _ _ _ (der_42457 v h) (by intro d hd; cases hd)))
def cl_53109 : CNF.NClause := [(75,false),(11,false),(92,false),(41,false),(54,false),(74,false),(69,false),(80,false),(83,false),(66,false),(90,false),(96,false),(112,false),(120,false),(98,false)]
theorem der_53109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53109 :=
  CNF.rup_sound cl_53109 [cl_42755,cl_51222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42755 v h) (hints_cons _ _ _ (der_51222 v h) (by intro d hd; cases hd)))
def cl_53117 : CNF.NClause := [(87,false),(4,false),(40,false),(81,false),(51,false),(75,false),(68,false),(73,false),(78,false),(83,false),(88,false),(123,false),(98,false),(101,false),(102,false)]
theorem der_53117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53117 :=
  CNF.rup_sound cl_53117 [cl_48098,cl_52090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48098 v h) (hints_cons _ _ _ (der_52090 v h) (by intro d hd; cases hd)))
def cl_53138 : CNF.NClause := [(94,false),(23,false),(13,false),(10,false),(76,false),(81,false),(92,false),(89,false),(75,false),(73,false),(83,false),(67,false),(109,false),(118,false),(99,false),(35,false)]
theorem der_53138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53138 :=
  CNF.rup_sound cl_53138 [cl_46205,cl_49765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_46205 v h) (hints_cons _ _ _ (der_49765 v h) (by intro d hd; cases hd)))
def cl_53151 : CNF.NClause := [(88,false),(33,false),(40,false),(17,false),(65,false),(18,true),(76,false),(64,false),(70,false),(69,false),(83,false),(77,false),(44,true),(112,false),(113,false),(106,false),(94,false)]
theorem der_53151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53151 :=
  CNF.rup_sound cl_53151 [cl_36811,cl_36802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36811 v h) (hints_cons _ _ _ (der_36802 v h) (by intro d hd; cases hd)))
def cl_53163 : CNF.NClause := [(97,false),(4,false),(37,false),(76,false),(87,false),(68,false),(73,false),(78,false),(80,true),(83,false),(63,false),(84,false),(91,false),(105,false),(101,false),(113,false),(43,false)]
theorem der_53163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53163 :=
  CNF.rup_sound cl_53163 [cl_41409,cl_49681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41409 v h) (hints_cons _ _ _ (der_49681 v h) (by intro d hd; cases hd)))
def cl_53169 : CNF.NClause := [(87,false),(4,false),(14,true),(48,false),(31,true),(34,false),(79,false),(70,false),(68,false),(73,false),(78,false),(83,false),(63,false),(96,false),(111,false),(116,false),(106,false)]
theorem der_53169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_53169 :=
  CNF.rup_sound cl_53169 [cl_42860,cl_49616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42860 v h) (hints_cons _ _ _ (der_49616 v h) (by intro d hd; cases hd)))
def chunk049 : List CNF.NClause := [cl_52038,cl_52039,cl_52040,cl_52041,cl_52042,cl_52043,cl_52044,cl_52045,cl_52046,cl_52047,cl_52048,cl_52049,cl_52050,cl_52051,cl_52052,cl_52053,cl_52054,cl_52055,cl_52056,cl_52057,cl_52058,cl_52059,cl_52061,cl_52063,cl_52064,cl_52065,cl_52066,cl_52067,cl_52068,cl_52069,cl_52070,cl_52073,cl_52077,cl_52078,cl_52081,cl_52083,cl_52084,cl_52085,cl_52087,cl_52088,cl_52089,cl_52090,cl_52091,cl_52092,cl_52093,cl_52094,cl_52095,cl_52097,cl_52099,cl_52100,cl_52101,cl_52102,cl_52103,cl_52104,cl_52105,cl_52107,cl_52109,cl_52110,cl_52111,cl_52112,cl_52113,cl_52114,cl_52115,cl_52116,cl_52117,cl_52118,cl_52119,cl_52127,cl_52128,cl_52132,cl_52134,cl_52135,cl_52136,cl_52137,cl_52140,cl_52142,cl_52143,cl_52146,cl_52147,cl_52149,cl_52150,cl_52151,cl_52153,cl_52155,cl_52157,cl_52158,cl_52159,cl_52160,cl_52162,cl_52163,cl_52164,cl_52166,cl_52167,cl_52169,cl_52171,cl_52172,cl_52177,cl_52178,cl_52181,cl_52182,cl_52184,cl_52185,cl_52186,cl_52187,cl_52188,cl_52189,cl_52190,cl_52191,cl_52193,cl_52194,cl_52195,cl_52197,cl_52198,cl_52199,cl_52201,cl_52202,cl_52208,cl_52210,cl_52212,cl_52214,cl_52215,cl_52218,cl_52219,cl_52220,cl_52222,cl_52223,cl_52224,cl_52225,cl_52227,cl_52228,cl_52229,cl_52232,cl_52234,cl_52235,cl_52236,cl_52237,cl_52238,cl_52240,cl_52241,cl_52242,cl_52244,cl_52246,cl_52249,cl_52251,cl_52253,cl_52254,cl_52256,cl_52257,cl_52258,cl_52259,cl_52260,cl_52261,cl_52263,cl_52265,cl_52266,cl_52267,cl_52268,cl_52269,cl_52270,cl_52271,cl_52272,cl_52273,cl_52277,cl_52278,cl_52279,cl_52280,cl_52281,cl_52282,cl_52284,cl_52286,cl_52287,cl_52288,cl_52290,cl_52291,cl_52292,cl_52293,cl_52295,cl_52296,cl_52297,cl_52298,cl_52299,cl_52300,cl_52301,cl_52302,cl_52304,cl_52305,cl_52309,cl_52312,cl_52313,cl_52315,cl_52316,cl_52317,cl_52318,cl_52319,cl_52322,cl_52324,cl_52325,cl_52327,cl_52328,cl_52329,cl_52332,cl_52333,cl_52337,cl_52338,cl_52340,cl_52341,cl_52342,cl_52344,cl_52345,cl_52346,cl_52347,cl_52349,cl_52350,cl_52352,cl_52353,cl_52355,cl_52357,cl_52360,cl_52361,cl_52362,cl_52365,cl_52367,cl_52368,cl_52369,cl_52371,cl_52372,cl_52373,cl_52376,cl_52377,cl_52378,cl_52382,cl_52383,cl_52386,cl_52391,cl_52392,cl_52395,cl_52396,cl_52399,cl_52400,cl_52401,cl_52403,cl_52404,cl_52405,cl_52406,cl_52407,cl_52408,cl_52409,cl_52410,cl_52411,cl_52412,cl_52413,cl_52414,cl_52415,cl_52416,cl_52417,cl_52419,cl_52420,cl_52421,cl_52422,cl_52425,cl_52426,cl_52427,cl_52429,cl_52430,cl_52431,cl_52432,cl_52435,cl_52437,cl_52438,cl_52442,cl_52443,cl_52444,cl_52445,cl_52446,cl_52447,cl_52448,cl_52449,cl_52450,cl_52460,cl_52463,cl_52464,cl_52465,cl_52468,cl_52470,cl_52471,cl_52472,cl_52473,cl_52474,cl_52478,cl_52479,cl_52481,cl_52485,cl_52486,cl_52487,cl_52489,cl_52491,cl_52492,cl_52493,cl_52494,cl_52495,cl_52497,cl_52498,cl_52500,cl_52502,cl_52503,cl_52504,cl_52505,cl_52506,cl_52507,cl_52510,cl_52511,cl_52514,cl_52515,cl_52516,cl_52517,cl_52518,cl_52519,cl_52521,cl_52522,cl_52523,cl_52524,cl_52525,cl_52526,cl_52527,cl_52528,cl_52534,cl_52535,cl_52538,cl_52540,cl_52543,cl_52547,cl_52553,cl_52554,cl_52556,cl_52558,cl_52560,cl_52561,cl_52563,cl_52565,cl_52569,cl_52573,cl_52576,cl_52577,cl_52578,cl_52588,cl_52589,cl_52592,cl_52594,cl_52595,cl_52596,cl_52599,cl_52601,cl_52602,cl_52604,cl_52605,cl_52606,cl_52608,cl_52609,cl_52611,cl_52612,cl_52615,cl_52616,cl_52621,cl_52622,cl_52627,cl_52629,cl_52632,cl_52633,cl_52634,cl_52636,cl_52637,cl_52638,cl_52639,cl_52640,cl_52642,cl_52643,cl_52647,cl_52649,cl_52650,cl_52652,cl_52653,cl_52658,cl_52660,cl_52662,cl_52663,cl_52666,cl_52670,cl_52671,cl_52676,cl_52680,cl_52685,cl_52686,cl_52688,cl_52689,cl_52691,cl_52693,cl_52696,cl_52697,cl_52700,cl_52701,cl_52702,cl_52703,cl_52706,cl_52707,cl_52709,cl_52711,cl_52713,cl_52714,cl_52715,cl_52716,cl_52717,cl_52720,cl_52722,cl_52723,cl_52724,cl_52725,cl_52730,cl_52731,cl_52733,cl_52734,cl_52736,cl_52741,cl_52743,cl_52749,cl_52752,cl_52753,cl_52754,cl_52755,cl_52758,cl_52759,cl_52760,cl_52762,cl_52763,cl_52764,cl_52765,cl_52772,cl_52775,cl_52777,cl_52778,cl_52779,cl_52780,cl_52781,cl_52782,cl_52783,cl_52784,cl_52789,cl_52792,cl_52794,cl_52796,cl_52797,cl_52799,cl_52800,cl_52803,cl_52812,cl_52816,cl_52817,cl_52819,cl_52820,cl_52821,cl_52822,cl_52823,cl_52824,cl_52828,cl_52829,cl_52830,cl_52834,cl_52837,cl_52840,cl_52846,cl_52851,cl_52858,cl_52859,cl_52870,cl_52872,cl_52876,cl_52879,cl_52880,cl_52885,cl_52889,cl_52892,cl_52898,cl_52901,cl_52908,cl_52958,cl_52970,cl_52974,cl_52991,cl_53006,cl_53033,cl_53078,cl_53081,cl_53084,cl_53085,cl_53103,cl_53109,cl_53117,cl_53138,cl_53151,cl_53163,cl_53169]
theorem chunk_sound049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk049, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_52038 v h) (hints_cons _ _ _ (der_52039 v h) (hints_cons _ _ _ (der_52040 v h) (hints_cons _ _ _ (der_52041 v h) (hints_cons _ _ _ (der_52042 v h) (hints_cons _ _ _ (der_52043 v h) (hints_cons _ _ _ (der_52044 v h) (hints_cons _ _ _ (der_52045 v h) (hints_cons _ _ _ (der_52046 v h) (hints_cons _ _ _ (der_52047 v h) (hints_cons _ _ _ (der_52048 v h) (hints_cons _ _ _ (der_52049 v h) (hints_cons _ _ _ (der_52050 v h) (hints_cons _ _ _ (der_52051 v h) (hints_cons _ _ _ (der_52052 v h) (hints_cons _ _ _ (der_52053 v h) (hints_cons _ _ _ (der_52054 v h) (hints_cons _ _ _ (der_52055 v h) (hints_cons _ _ _ (der_52056 v h) (hints_cons _ _ _ (der_52057 v h) (hints_cons _ _ _ (der_52058 v h) (hints_cons _ _ _ (der_52059 v h) (hints_cons _ _ _ (der_52061 v h) (hints_cons _ _ _ (der_52063 v h) (hints_cons _ _ _ (der_52064 v h) (hints_cons _ _ _ (der_52065 v h) (hints_cons _ _ _ (der_52066 v h) (hints_cons _ _ _ (der_52067 v h) (hints_cons _ _ _ (der_52068 v h) (hints_cons _ _ _ (der_52069 v h) (hints_cons _ _ _ (der_52070 v h) (hints_cons _ _ _ (der_52073 v h) (hints_cons _ _ _ (der_52077 v h) (hints_cons _ _ _ (der_52078 v h) (hints_cons _ _ _ (der_52081 v h) (hints_cons _ _ _ (der_52083 v h) (hints_cons _ _ _ (der_52084 v h) (hints_cons _ _ _ (der_52085 v h) (hints_cons _ _ _ (der_52087 v h) (hints_cons _ _ _ (der_52088 v h) (hints_cons _ _ _ (der_52089 v h) (hints_cons _ _ _ (der_52090 v h) (hints_cons _ _ _ (der_52091 v h) (hints_cons _ _ _ (der_52092 v h) (hints_cons _ _ _ (der_52093 v h) (hints_cons _ _ _ (der_52094 v h) (hints_cons _ _ _ (der_52095 v h) (hints_cons _ _ _ (der_52097 v h) (hints_cons _ _ _ (der_52099 v h) (hints_cons _ _ _ (der_52100 v h) (hints_cons _ _ _ (der_52101 v h) (hints_cons _ _ _ (der_52102 v h) (hints_cons _ _ _ (der_52103 v h) (hints_cons _ _ _ (der_52104 v h) (hints_cons _ _ _ (der_52105 v h) (hints_cons _ _ _ (der_52107 v h) (hints_cons _ _ _ (der_52109 v h) (hints_cons _ _ _ (der_52110 v h) (hints_cons _ _ _ (der_52111 v h) (hints_cons _ _ _ (der_52112 v h) (hints_cons _ _ _ (der_52113 v h) (hints_cons _ _ _ (der_52114 v h) (hints_cons _ _ _ (der_52115 v h) (hints_cons _ _ _ (der_52116 v h) (hints_cons _ _ _ (der_52117 v h) (hints_cons _ _ _ (der_52118 v h) (hints_cons _ _ _ (der_52119 v h) (hints_cons _ _ _ (der_52127 v h) (hints_cons _ _ _ (der_52128 v h) (hints_cons _ _ _ (der_52132 v h) (hints_cons _ _ _ (der_52134 v h) (hints_cons _ _ _ (der_52135 v h) (hints_cons _ _ _ (der_52136 v h) (hints_cons _ _ _ (der_52137 v h) (hints_cons _ _ _ (der_52140 v h) (hints_cons _ _ _ (der_52142 v h) (hints_cons _ _ _ (der_52143 v h) (hints_cons _ _ _ (der_52146 v h) (hints_cons _ _ _ (der_52147 v h) (hints_cons _ _ _ (der_52149 v h) (hints_cons _ _ _ (der_52150 v h) (hints_cons _ _ _ (der_52151 v h) (hints_cons _ _ _ (der_52153 v h) (hints_cons _ _ _ (der_52155 v h) (hints_cons _ _ _ (der_52157 v h) (hints_cons _ _ _ (der_52158 v h) (hints_cons _ _ _ (der_52159 v h) (hints_cons _ _ _ (der_52160 v h) (hints_cons _ _ _ (der_52162 v h) (hints_cons _ _ _ (der_52163 v h) (hints_cons _ _ _ (der_52164 v h) (hints_cons _ _ _ (der_52166 v h) (hints_cons _ _ _ (der_52167 v h) (hints_cons _ _ _ (der_52169 v h) (hints_cons _ _ _ (der_52171 v h) (hints_cons _ _ _ (der_52172 v h) (hints_cons _ _ _ (der_52177 v h) (hints_cons _ _ _ (der_52178 v h) (hints_cons _ _ _ (der_52181 v h) (hints_cons _ _ _ (der_52182 v h) (hints_cons _ _ _ (der_52184 v h) (hints_cons _ _ _ (der_52185 v h) (hints_cons _ _ _ (der_52186 v h) (hints_cons _ _ _ (der_52187 v h) (hints_cons _ _ _ (der_52188 v h) (hints_cons _ _ _ (der_52189 v h) (hints_cons _ _ _ (der_52190 v h) (hints_cons _ _ _ (der_52191 v h) (hints_cons _ _ _ (der_52193 v h) (hints_cons _ _ _ (der_52194 v h) (hints_cons _ _ _ (der_52195 v h) (hints_cons _ _ _ (der_52197 v h) (hints_cons _ _ _ (der_52198 v h) (hints_cons _ _ _ (der_52199 v h) (hints_cons _ _ _ (der_52201 v h) (hints_cons _ _ _ (der_52202 v h) (hints_cons _ _ _ (der_52208 v h) (hints_cons _ _ _ (der_52210 v h) (hints_cons _ _ _ (der_52212 v h) (hints_cons _ _ _ (der_52214 v h) (hints_cons _ _ _ (der_52215 v h) (hints_cons _ _ _ (der_52218 v h) (hints_cons _ _ _ (der_52219 v h) (hints_cons _ _ _ (der_52220 v h) (hints_cons _ _ _ (der_52222 v h) (hints_cons _ _ _ (der_52223 v h) (hints_cons _ _ _ (der_52224 v h) (hints_cons _ _ _ (der_52225 v h) (hints_cons _ _ _ (der_52227 v h) (hints_cons _ _ _ (der_52228 v h) (hints_cons _ _ _ (der_52229 v h) (hints_cons _ _ _ (der_52232 v h) (hints_cons _ _ _ (der_52234 v h) (hints_cons _ _ _ (der_52235 v h) (hints_cons _ _ _ (der_52236 v h) (hints_cons _ _ _ (der_52237 v h) (hints_cons _ _ _ (der_52238 v h) (hints_cons _ _ _ (der_52240 v h) (hints_cons _ _ _ (der_52241 v h) (hints_cons _ _ _ (der_52242 v h) (hints_cons _ _ _ (der_52244 v h) (hints_cons _ _ _ (der_52246 v h) (hints_cons _ _ _ (der_52249 v h) (hints_cons _ _ _ (der_52251 v h) (hints_cons _ _ _ (der_52253 v h) (hints_cons _ _ _ (der_52254 v h) (hints_cons _ _ _ (der_52256 v h) (hints_cons _ _ _ (der_52257 v h) (hints_cons _ _ _ (der_52258 v h) (hints_cons _ _ _ (der_52259 v h) (hints_cons _ _ _ (der_52260 v h) (hints_cons _ _ _ (der_52261 v h) (hints_cons _ _ _ (der_52263 v h) (hints_cons _ _ _ (der_52265 v h) (hints_cons _ _ _ (der_52266 v h) (hints_cons _ _ _ (der_52267 v h) (hints_cons _ _ _ (der_52268 v h) (hints_cons _ _ _ (der_52269 v h) (hints_cons _ _ _ (der_52270 v h) (hints_cons _ _ _ (der_52271 v h) (hints_cons _ _ _ (der_52272 v h) (hints_cons _ _ _ (der_52273 v h) (hints_cons _ _ _ (der_52277 v h) (hints_cons _ _ _ (der_52278 v h) (hints_cons _ _ _ (der_52279 v h) (hints_cons _ _ _ (der_52280 v h) (hints_cons _ _ _ (der_52281 v h) (hints_cons _ _ _ (der_52282 v h) (hints_cons _ _ _ (der_52284 v h) (hints_cons _ _ _ (der_52286 v h) (hints_cons _ _ _ (der_52287 v h) (hints_cons _ _ _ (der_52288 v h) (hints_cons _ _ _ (der_52290 v h) (hints_cons _ _ _ (der_52291 v h) (hints_cons _ _ _ (der_52292 v h) (hints_cons _ _ _ (der_52293 v h) (hints_cons _ _ _ (der_52295 v h) (hints_cons _ _ _ (der_52296 v h) (hints_cons _ _ _ (der_52297 v h) (hints_cons _ _ _ (der_52298 v h) (hints_cons _ _ _ (der_52299 v h) (hints_cons _ _ _ (der_52300 v h) (hints_cons _ _ _ (der_52301 v h) (hints_cons _ _ _ (der_52302 v h) (hints_cons _ _ _ (der_52304 v h) (hints_cons _ _ _ (der_52305 v h) (hints_cons _ _ _ (der_52309 v h) (hints_cons _ _ _ (der_52312 v h) (hints_cons _ _ _ (der_52313 v h) (hints_cons _ _ _ (der_52315 v h) (hints_cons _ _ _ (der_52316 v h) (hints_cons _ _ _ (der_52317 v h) (hints_cons _ _ _ (der_52318 v h) (hints_cons _ _ _ (der_52319 v h) (hints_cons _ _ _ (der_52322 v h) (hints_cons _ _ _ (der_52324 v h) (hints_cons _ _ _ (der_52325 v h) (hints_cons _ _ _ (der_52327 v h) (hints_cons _ _ _ (der_52328 v h) (hints_cons _ _ _ (der_52329 v h) (hints_cons _ _ _ (der_52332 v h) (hints_cons _ _ _ (der_52333 v h) (hints_cons _ _ _ (der_52337 v h) (hints_cons _ _ _ (der_52338 v h) (hints_cons _ _ _ (der_52340 v h) (hints_cons _ _ _ (der_52341 v h) (hints_cons _ _ _ (der_52342 v h) (hints_cons _ _ _ (der_52344 v h) (hints_cons _ _ _ (der_52345 v h) (hints_cons _ _ _ (der_52346 v h) (hints_cons _ _ _ (der_52347 v h) (hints_cons _ _ _ (der_52349 v h) (hints_cons _ _ _ (der_52350 v h) (hints_cons _ _ _ (der_52352 v h) (hints_cons _ _ _ (der_52353 v h) (hints_cons _ _ _ (der_52355 v h) (hints_cons _ _ _ (der_52357 v h) (hints_cons _ _ _ (der_52360 v h) (hints_cons _ _ _ (der_52361 v h) (hints_cons _ _ _ (der_52362 v h) (hints_cons _ _ _ (der_52365 v h) (hints_cons _ _ _ (der_52367 v h) (hints_cons _ _ _ (der_52368 v h) (hints_cons _ _ _ (der_52369 v h) (hints_cons _ _ _ (der_52371 v h) (hints_cons _ _ _ (der_52372 v h) (hints_cons _ _ _ (der_52373 v h) (hints_cons _ _ _ (der_52376 v h) (hints_cons _ _ _ (der_52377 v h) (hints_cons _ _ _ (der_52378 v h) (hints_cons _ _ _ (der_52382 v h) (hints_cons _ _ _ (der_52383 v h) (hints_cons _ _ _ (der_52386 v h) (hints_cons _ _ _ (der_52391 v h) (hints_cons _ _ _ (der_52392 v h) (hints_cons _ _ _ (der_52395 v h) (hints_cons _ _ _ (der_52396 v h) (hints_cons _ _ _ (der_52399 v h) (hints_cons _ _ _ (der_52400 v h) (hints_cons _ _ _ (der_52401 v h) (hints_cons _ _ _ (der_52403 v h) (hints_cons _ _ _ (der_52404 v h) (hints_cons _ _ _ (der_52405 v h) (hints_cons _ _ _ (der_52406 v h) (hints_cons _ _ _ (der_52407 v h) (hints_cons _ _ _ (der_52408 v h) (hints_cons _ _ _ (der_52409 v h) (hints_cons _ _ _ (der_52410 v h) (hints_cons _ _ _ (der_52411 v h) (hints_cons _ _ _ (der_52412 v h) (hints_cons _ _ _ (der_52413 v h) (hints_cons _ _ _ (der_52414 v h) (hints_cons _ _ _ (der_52415 v h) (hints_cons _ _ _ (der_52416 v h) (hints_cons _ _ _ (der_52417 v h) (hints_cons _ _ _ (der_52419 v h) (hints_cons _ _ _ (der_52420 v h) (hints_cons _ _ _ (der_52421 v h) (hints_cons _ _ _ (der_52422 v h) (hints_cons _ _ _ (der_52425 v h) (hints_cons _ _ _ (der_52426 v h) (hints_cons _ _ _ (der_52427 v h) (hints_cons _ _ _ (der_52429 v h) (hints_cons _ _ _ (der_52430 v h) (hints_cons _ _ _ (der_52431 v h) (hints_cons _ _ _ (der_52432 v h) (hints_cons _ _ _ (der_52435 v h) (hints_cons _ _ _ (der_52437 v h) (hints_cons _ _ _ (der_52438 v h) (hints_cons _ _ _ (der_52442 v h) (hints_cons _ _ _ (der_52443 v h) (hints_cons _ _ _ (der_52444 v h) (hints_cons _ _ _ (der_52445 v h) (hints_cons _ _ _ (der_52446 v h) (hints_cons _ _ _ (der_52447 v h) (hints_cons _ _ _ (der_52448 v h) (hints_cons _ _ _ (der_52449 v h) (hints_cons _ _ _ (der_52450 v h) (hints_cons _ _ _ (der_52460 v h) (hints_cons _ _ _ (der_52463 v h) (hints_cons _ _ _ (der_52464 v h) (hints_cons _ _ _ (der_52465 v h) (hints_cons _ _ _ (der_52468 v h) (hints_cons _ _ _ (der_52470 v h) (hints_cons _ _ _ (der_52471 v h) (hints_cons _ _ _ (der_52472 v h) (hints_cons _ _ _ (der_52473 v h) (hints_cons _ _ _ (der_52474 v h) (hints_cons _ _ _ (der_52478 v h) (hints_cons _ _ _ (der_52479 v h) (hints_cons _ _ _ (der_52481 v h) (hints_cons _ _ _ (der_52485 v h) (hints_cons _ _ _ (der_52486 v h) (hints_cons _ _ _ (der_52487 v h) (hints_cons _ _ _ (der_52489 v h) (hints_cons _ _ _ (der_52491 v h) (hints_cons _ _ _ (der_52492 v h) (hints_cons _ _ _ (der_52493 v h) (hints_cons _ _ _ (der_52494 v h) (hints_cons _ _ _ (der_52495 v h) (hints_cons _ _ _ (der_52497 v h) (hints_cons _ _ _ (der_52498 v h) (hints_cons _ _ _ (der_52500 v h) (hints_cons _ _ _ (der_52502 v h) (hints_cons _ _ _ (der_52503 v h) (hints_cons _ _ _ (der_52504 v h) (hints_cons _ _ _ (der_52505 v h) (hints_cons _ _ _ (der_52506 v h) (hints_cons _ _ _ (der_52507 v h) (hints_cons _ _ _ (der_52510 v h) (hints_cons _ _ _ (der_52511 v h) (hints_cons _ _ _ (der_52514 v h) (hints_cons _ _ _ (der_52515 v h) (hints_cons _ _ _ (der_52516 v h) (hints_cons _ _ _ (der_52517 v h) (hints_cons _ _ _ (der_52518 v h) (hints_cons _ _ _ (der_52519 v h) (hints_cons _ _ _ (der_52521 v h) (hints_cons _ _ _ (der_52522 v h) (hints_cons _ _ _ (der_52523 v h) (hints_cons _ _ _ (der_52524 v h) (hints_cons _ _ _ (der_52525 v h) (hints_cons _ _ _ (der_52526 v h) (hints_cons _ _ _ (der_52527 v h) (hints_cons _ _ _ (der_52528 v h) (hints_cons _ _ _ (der_52534 v h) (hints_cons _ _ _ (der_52535 v h) (hints_cons _ _ _ (der_52538 v h) (hints_cons _ _ _ (der_52540 v h) (hints_cons _ _ _ (der_52543 v h) (hints_cons _ _ _ (der_52547 v h) (hints_cons _ _ _ (der_52553 v h) (hints_cons _ _ _ (der_52554 v h) (hints_cons _ _ _ (der_52556 v h) (hints_cons _ _ _ (der_52558 v h) (hints_cons _ _ _ (der_52560 v h) (hints_cons _ _ _ (der_52561 v h) (hints_cons _ _ _ (der_52563 v h) (hints_cons _ _ _ (der_52565 v h) (hints_cons _ _ _ (der_52569 v h) (hints_cons _ _ _ (der_52573 v h) (hints_cons _ _ _ (der_52576 v h) (hints_cons _ _ _ (der_52577 v h) (hints_cons _ _ _ (der_52578 v h) (hints_cons _ _ _ (der_52588 v h) (hints_cons _ _ _ (der_52589 v h) (hints_cons _ _ _ (der_52592 v h) (hints_cons _ _ _ (der_52594 v h) (hints_cons _ _ _ (der_52595 v h) (hints_cons _ _ _ (der_52596 v h) (hints_cons _ _ _ (der_52599 v h) (hints_cons _ _ _ (der_52601 v h) (hints_cons _ _ _ (der_52602 v h) (hints_cons _ _ _ (der_52604 v h) (hints_cons _ _ _ (der_52605 v h) (hints_cons _ _ _ (der_52606 v h) (hints_cons _ _ _ (der_52608 v h) (hints_cons _ _ _ (der_52609 v h) (hints_cons _ _ _ (der_52611 v h) (hints_cons _ _ _ (der_52612 v h) (hints_cons _ _ _ (der_52615 v h) (hints_cons _ _ _ (der_52616 v h) (hints_cons _ _ _ (der_52621 v h) (hints_cons _ _ _ (der_52622 v h) (hints_cons _ _ _ (der_52627 v h) (hints_cons _ _ _ (der_52629 v h) (hints_cons _ _ _ (der_52632 v h) (hints_cons _ _ _ (der_52633 v h) (hints_cons _ _ _ (der_52634 v h) (hints_cons _ _ _ (der_52636 v h) (hints_cons _ _ _ (der_52637 v h) (hints_cons _ _ _ (der_52638 v h) (hints_cons _ _ _ (der_52639 v h) (hints_cons _ _ _ (der_52640 v h) (hints_cons _ _ _ (der_52642 v h) (hints_cons _ _ _ (der_52643 v h) (hints_cons _ _ _ (der_52647 v h) (hints_cons _ _ _ (der_52649 v h) (hints_cons _ _ _ (der_52650 v h) (hints_cons _ _ _ (der_52652 v h) (hints_cons _ _ _ (der_52653 v h) (hints_cons _ _ _ (der_52658 v h) (hints_cons _ _ _ (der_52660 v h) (hints_cons _ _ _ (der_52662 v h) (hints_cons _ _ _ (der_52663 v h) (hints_cons _ _ _ (der_52666 v h) (hints_cons _ _ _ (der_52670 v h) (hints_cons _ _ _ (der_52671 v h) (hints_cons _ _ _ (der_52676 v h) (hints_cons _ _ _ (der_52680 v h) (hints_cons _ _ _ (der_52685 v h) (hints_cons _ _ _ (der_52686 v h) (hints_cons _ _ _ (der_52688 v h) (hints_cons _ _ _ (der_52689 v h) (hints_cons _ _ _ (der_52691 v h) (hints_cons _ _ _ (der_52693 v h) (hints_cons _ _ _ (der_52696 v h) (hints_cons _ _ _ (der_52697 v h) (hints_cons _ _ _ (der_52700 v h) (hints_cons _ _ _ (der_52701 v h) (hints_cons _ _ _ (der_52702 v h) (hints_cons _ _ _ (der_52703 v h) (hints_cons _ _ _ (der_52706 v h) (hints_cons _ _ _ (der_52707 v h) (hints_cons _ _ _ (der_52709 v h) (hints_cons _ _ _ (der_52711 v h) (hints_cons _ _ _ (der_52713 v h) (hints_cons _ _ _ (der_52714 v h) (hints_cons _ _ _ (der_52715 v h) (hints_cons _ _ _ (der_52716 v h) (hints_cons _ _ _ (der_52717 v h) (hints_cons _ _ _ (der_52720 v h) (hints_cons _ _ _ (der_52722 v h) (hints_cons _ _ _ (der_52723 v h) (hints_cons _ _ _ (der_52724 v h) (hints_cons _ _ _ (der_52725 v h) (hints_cons _ _ _ (der_52730 v h) (hints_cons _ _ _ (der_52731 v h) (hints_cons _ _ _ (der_52733 v h) (hints_cons _ _ _ (der_52734 v h) (hints_cons _ _ _ (der_52736 v h) (hints_cons _ _ _ (der_52741 v h) (hints_cons _ _ _ (der_52743 v h) (hints_cons _ _ _ (der_52749 v h) (hints_cons _ _ _ (der_52752 v h) (hints_cons _ _ _ (der_52753 v h) (hints_cons _ _ _ (der_52754 v h) (hints_cons _ _ _ (der_52755 v h) (hints_cons _ _ _ (der_52758 v h) (hints_cons _ _ _ (der_52759 v h) (hints_cons _ _ _ (der_52760 v h) (hints_cons _ _ _ (der_52762 v h) (hints_cons _ _ _ (der_52763 v h) (hints_cons _ _ _ (der_52764 v h) (hints_cons _ _ _ (der_52765 v h) (hints_cons _ _ _ (der_52772 v h) (hints_cons _ _ _ (der_52775 v h) (hints_cons _ _ _ (der_52777 v h) (hints_cons _ _ _ (der_52778 v h) (hints_cons _ _ _ (der_52779 v h) (hints_cons _ _ _ (der_52780 v h) (hints_cons _ _ _ (der_52781 v h) (hints_cons _ _ _ (der_52782 v h) (hints_cons _ _ _ (der_52783 v h) (hints_cons _ _ _ (der_52784 v h) (hints_cons _ _ _ (der_52789 v h) (hints_cons _ _ _ (der_52792 v h) (hints_cons _ _ _ (der_52794 v h) (hints_cons _ _ _ (der_52796 v h) (hints_cons _ _ _ (der_52797 v h) (hints_cons _ _ _ (der_52799 v h) (hints_cons _ _ _ (der_52800 v h) (hints_cons _ _ _ (der_52803 v h) (hints_cons _ _ _ (der_52812 v h) (hints_cons _ _ _ (der_52816 v h) (hints_cons _ _ _ (der_52817 v h) (hints_cons _ _ _ (der_52819 v h) (hints_cons _ _ _ (der_52820 v h) (hints_cons _ _ _ (der_52821 v h) (hints_cons _ _ _ (der_52822 v h) (hints_cons _ _ _ (der_52823 v h) (hints_cons _ _ _ (der_52824 v h) (hints_cons _ _ _ (der_52828 v h) (hints_cons _ _ _ (der_52829 v h) (hints_cons _ _ _ (der_52830 v h) (hints_cons _ _ _ (der_52834 v h) (hints_cons _ _ _ (der_52837 v h) (hints_cons _ _ _ (der_52840 v h) (hints_cons _ _ _ (der_52846 v h) (hints_cons _ _ _ (der_52851 v h) (hints_cons _ _ _ (der_52858 v h) (hints_cons _ _ _ (der_52859 v h) (hints_cons _ _ _ (der_52870 v h) (hints_cons _ _ _ (der_52872 v h) (hints_cons _ _ _ (der_52876 v h) (hints_cons _ _ _ (der_52879 v h) (hints_cons _ _ _ (der_52880 v h) (hints_cons _ _ _ (der_52885 v h) (hints_cons _ _ _ (der_52889 v h) (hints_cons _ _ _ (der_52892 v h) (hints_cons _ _ _ (der_52898 v h) (hints_cons _ _ _ (der_52901 v h) (hints_cons _ _ _ (der_52908 v h) (hints_cons _ _ _ (der_52958 v h) (hints_cons _ _ _ (der_52970 v h) (hints_cons _ _ _ (der_52974 v h) (hints_cons _ _ _ (der_52991 v h) (hints_cons _ _ _ (der_53006 v h) (hints_cons _ _ _ (der_53033 v h) (hints_cons _ _ _ (der_53078 v h) (hints_cons _ _ _ (der_53081 v h) (hints_cons _ _ _ (der_53084 v h) (hints_cons _ _ _ (der_53085 v h) (hints_cons _ _ _ (der_53103 v h) (hints_cons _ _ _ (der_53109 v h) (hints_cons _ _ _ (der_53117 v h) (hints_cons _ _ _ (der_53138 v h) (hints_cons _ _ _ (der_53151 v h) (hints_cons _ _ _ (der_53163 v h) (hints_cons _ _ _ (der_53169 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix049 := prefix048 ++ chunk049
theorem prefix_sound049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix049, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound048 v h c hc
  · exact chunk_sound049 v h c hc
end Percolation.NReplay
