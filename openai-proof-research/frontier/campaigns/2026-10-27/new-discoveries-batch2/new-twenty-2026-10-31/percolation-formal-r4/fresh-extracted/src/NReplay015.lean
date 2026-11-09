import NReplay014
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_29960 : CNF.NClause := [(65,false),(13,true),(23,true),(18,true),(3,true)]
theorem der_29960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29960 :=
  CNF.rup_sound cl_29960 [cl_15108,cl_23277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15108 v h) (hints_cons _ _ _ (der_23277 v h) (by intro d hd; cases hd)))
def cl_29961 : CNF.NClause := [(74,true),(2,true),(29,true),(23,false),(6,false)]
theorem der_29961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29961 :=
  CNF.rup_sound cl_29961 [cl_23526,cl_23525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23526 v h) (hints_cons _ _ _ (der_23525 v h) (by intro d hd; cases hd)))
def cl_29962 : CNF.NClause := [(74,true),(2,true),(29,true),(19,false),(6,false)]
theorem der_29962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29962 :=
  CNF.rup_sound cl_29962 [cl_23528,cl_23527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23528 v h) (hints_cons _ _ _ (der_23527 v h) (by intro d hd; cases hd)))
def cl_29963 : CNF.NClause := [(83,true),(4,true),(11,true),(26,false),(5,false)]
theorem der_29963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29963 :=
  CNF.rup_sound cl_29963 [cl_23532,cl_23531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23532 v h) (hints_cons _ _ _ (der_23531 v h) (by intro d hd; cases hd)))
def cl_29964 : CNF.NClause := [(83,true),(4,true),(23,false),(5,false),(11,true)]
theorem der_29964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29964 :=
  CNF.rup_sound cl_29964 [cl_23534,cl_23533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23534 v h) (hints_cons _ _ _ (der_23533 v h) (by intro d hd; cases hd)))
def cl_29965 : CNF.NClause := [(73,true),(10,false),(28,false),(7,false),(21,false)]
theorem der_29965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29965 :=
  CNF.rup_sound cl_29965 [cl_23537,cl_29805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23537 v h) (hints_cons _ _ _ (der_29805 v h) (by intro d hd; cases hd)))
def cl_29967 : CNF.NClause := [(73,true),(7,false),(18,false),(10,false),(28,false)]
theorem der_29967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29967 :=
  CNF.rup_sound cl_29967 [cl_23539,cl_23535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23539 v h) (hints_cons _ _ _ (der_23535 v h) (by intro d hd; cases hd)))
def cl_29968 : CNF.NClause := [(73,true),(4,true),(28,false),(18,false),(7,false)]
theorem der_29968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29968 :=
  CNF.rup_sound cl_29968 [cl_23540,cl_29967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23540 v h) (hints_cons _ _ _ (der_29967 v h) (by intro d hd; cases hd)))
def cl_29969 : CNF.NClause := [(7,false),(73,true),(21,true),(10,false),(28,false)]
theorem der_29969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29969 :=
  CNF.rup_sound cl_29969 [cl_23541,cl_29967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23541 v h) (hints_cons _ _ _ (der_29967 v h) (by intro d hd; cases hd)))
def cl_29970 : CNF.NClause := [(73,true),(21,true),(4,true),(28,false),(7,false)]
theorem der_29970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29970 :=
  CNF.rup_sound cl_29970 [cl_23542,cl_29969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23542 v h) (hints_cons _ _ _ (der_29969 v h) (by intro d hd; cases hd)))
def cl_29971 : CNF.NClause := [(73,true),(4,true),(18,false),(7,false),(21,false)]
theorem der_29971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29971 :=
  CNF.rup_sound cl_29971 [cl_23544,cl_23543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23544 v h) (hints_cons _ _ _ (der_23543 v h) (by intro d hd; cases hd)))
def cl_29972 : CNF.NClause := [(4,true),(7,false),(73,true),(10,false),(21,false)]
theorem der_29972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29972 :=
  CNF.rup_sound cl_29972 [cl_23545,cl_23543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23545 v h) (hints_cons _ _ _ (der_23543 v h) (by intro d hd; cases hd)))
def cl_29973 : CNF.NClause := [(73,true),(7,false),(18,true),(4,true),(21,false)]
theorem der_29973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29973 :=
  CNF.rup_sound cl_29973 [cl_23546,cl_29972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23546 v h) (hints_cons _ _ _ (der_29972 v h) (by intro d hd; cases hd)))
def cl_29974 : CNF.NClause := [(10,false),(73,true),(4,true),(18,false),(7,false)]
theorem der_29974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29974 :=
  CNF.rup_sound cl_29974 [cl_23547,cl_29968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23547 v h) (hints_cons _ _ _ (der_29968 v h) (by intro d hd; cases hd)))
def cl_29975 : CNF.NClause := [(73,true),(21,true),(4,true),(18,false),(7,false)]
theorem der_29975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29975 :=
  CNF.rup_sound cl_29975 [cl_23548,cl_29974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23548 v h) (hints_cons _ _ _ (der_29974 v h) (by intro d hd; cases hd)))
def cl_29976 : CNF.NClause := [(28,true),(7,false),(4,true),(73,true),(10,false)]
theorem der_29976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29976 :=
  CNF.rup_sound cl_29976 [cl_23549,cl_29972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23549 v h) (hints_cons _ _ _ (der_29972 v h) (by intro d hd; cases hd)))
def cl_29977 : CNF.NClause := [(21,true),(66,false),(16,true),(6,true),(11,true)]
theorem der_29977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29977 :=
  CNF.rup_sound cl_29977 [cl_15141,cl_23196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15141 v h) (hints_cons _ _ _ (der_23196 v h) (by intro d hd; cases hd)))
def cl_29980 : CNF.NClause := [(75,true),(26,true),(10,false),(16,true),(9,false)]
theorem der_29980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29980 :=
  CNF.rup_sound cl_29980 [cl_23559,cl_23558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23559 v h) (hints_cons _ _ _ (der_23558 v h) (by intro d hd; cases hd)))
def cl_29981 : CNF.NClause := [(68,true),(29,false),(16,true),(4,false),(8,false)]
theorem der_29981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29981 :=
  CNF.rup_sound cl_29981 [cl_23561,cl_23560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23561 v h) (hints_cons _ _ _ (der_23560 v h) (by intro d hd; cases hd)))
def cl_29982 : CNF.NClause := [(68,true),(16,true),(20,false),(4,false),(8,false)]
theorem der_29982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29982 :=
  CNF.rup_sound cl_29982 [cl_23562,cl_29981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23562 v h) (hints_cons _ _ _ (der_29981 v h) (by intro d hd; cases hd)))
def cl_29983 : CNF.NClause := [(68,true),(16,true),(20,true),(4,false),(8,false)]
theorem der_29983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29983 :=
  CNF.rup_sound cl_29983 [cl_23563,cl_29981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23563 v h) (hints_cons _ _ _ (der_29981 v h) (by intro d hd; cases hd)))
def cl_29984 : CNF.NClause := [(68,true),(12,true),(16,true),(4,false),(29,false)]
theorem der_29984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29984 :=
  CNF.rup_sound cl_29984 [cl_23564,cl_23554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23564 v h) (hints_cons _ _ _ (der_23554 v h) (by intro d hd; cases hd)))
def cl_29986 : CNF.NClause := [(66,false),(6,true),(11,true),(1,true),(16,true)]
theorem der_29986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29986 :=
  CNF.rup_sound cl_29986 [cl_15126,cl_23196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15126 v h) (hints_cons _ _ _ (der_23196 v h) (by intro d hd; cases hd)))
def cl_29987 : CNF.NClause := [(75,true),(3,true),(16,true),(26,false),(9,false)]
theorem der_29987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29987 :=
  CNF.rup_sound cl_29987 [cl_23567,cl_23565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23567 v h) (hints_cons _ _ _ (der_23565 v h) (by intro d hd; cases hd)))
def cl_29988 : CNF.NClause := [(89,false),(23,true),(16,true),(7,true),(27,true)]
theorem der_29988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29988 :=
  CNF.rup_sound cl_29988 [cl_15342,cl_29820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15342 v h) (hints_cons _ _ _ (der_29820 v h) (by intro d hd; cases hd)))
def cl_29989 : CNF.NClause := [(77,false),(16,true),(18,true),(15,true),(17,true)]
theorem der_29989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29989 :=
  CNF.rup_sound cl_29989 [cl_15222,cl_23222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15222 v h) (hints_cons _ _ _ (der_23222 v h) (by intro d hd; cases hd)))
def cl_29990 : CNF.NClause := [(77,false),(19,true),(17,true),(16,true),(15,true)]
theorem der_29990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29990 :=
  CNF.rup_sound cl_29990 [cl_15230,cl_23222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15230 v h) (hints_cons _ _ _ (der_23222 v h) (by intro d hd; cases hd)))
def cl_29991 : CNF.NClause := [(64,false),(12,true),(2,true),(7,true),(22,true)]
theorem der_29991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29991 :=
  CNF.rup_sound cl_29991 [cl_15070,cl_23353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15070 v h) (hints_cons _ _ _ (der_23353 v h) (by intro d hd; cases hd)))
def cl_29992 : CNF.NClause := [(91,true),(24,false),(26,false),(12,true),(18,true)]
theorem der_29992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29992 :=
  CNF.rup_sound cl_29992 [cl_15384,cl_29889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15384 v h) (hints_cons _ _ _ (der_29889 v h) (by intro d hd; cases hd)))
def cl_29993 : CNF.NClause := [(91,false),(6,true),(12,true),(18,true),(24,true)]
theorem der_29993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29993 :=
  CNF.rup_sound cl_29993 [cl_15392,cl_23206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15392 v h) (hints_cons _ _ _ (der_23206 v h) (by intro d hd; cases hd)))
def cl_29994 : CNF.NClause := [(91,false),(18,true),(12,true),(6,true),(26,true)]
theorem der_29994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29994 :=
  CNF.rup_sound cl_29994 [cl_15400,cl_23206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15400 v h) (hints_cons _ _ _ (der_23206 v h) (by intro d hd; cases hd)))
def cl_29995 : CNF.NClause := [(7,false),(73,true),(10,false),(18,true),(21,false)]
theorem der_29995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29995 :=
  CNF.rup_sound cl_29995 [cl_23577,cl_29965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23577 v h) (hints_cons _ _ _ (der_29965 v h) (by intro d hd; cases hd)))
def cl_29996 : CNF.NClause := [(18,true),(7,false),(73,true),(10,false),(4,false)]
theorem der_29996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29996 :=
  CNF.rup_sound cl_29996 [cl_23578,cl_29995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23578 v h) (hints_cons _ _ _ (der_29995 v h) (by intro d hd; cases hd)))
def cl_29998 : CNF.NClause := [(69,true),(2,true),(18,true),(20,false),(9,false)]
theorem der_29998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29998 :=
  CNF.rup_sound cl_29998 [cl_23581,cl_23579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23581 v h) (hints_cons _ _ _ (der_23579 v h) (by intro d hd; cases hd)))
def cl_29999 : CNF.NClause := [(69,true),(18,true),(2,true),(11,false),(9,false)]
theorem der_29999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29999 :=
  CNF.rup_sound cl_29999 [cl_23582,cl_29998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23582 v h) (hints_cons _ _ _ (der_29998 v h) (by intro d hd; cases hd)))
def cl_30000 : CNF.NClause := [(69,true),(11,false),(18,true),(20,true),(9,false)]
theorem der_30000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30000 :=
  CNF.rup_sound cl_30000 [cl_23585,cl_29999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23585 v h) (hints_cons _ _ _ (der_29999 v h) (by intro d hd; cases hd)))
def cl_30001 : CNF.NClause := [(65,false),(18,true),(23,true),(13,true),(8,true)]
theorem der_30001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30001 :=
  CNF.rup_sound cl_30001 [cl_15109,cl_23277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15109 v h) (hints_cons _ _ _ (der_23277 v h) (by intro d hd; cases hd)))
def cl_30002 : CNF.NClause := [(18,true),(73,true),(4,false),(21,true),(10,false)]
theorem der_30002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30002 :=
  CNF.rup_sound cl_30002 [cl_23590,cl_29996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23590 v h) (hints_cons _ _ _ (der_29996 v h) (by intro d hd; cases hd)))
def cl_30003 : CNF.NClause := [(28,false),(73,true),(10,false),(18,true),(21,false)]
theorem der_30003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30003 :=
  CNF.rup_sound cl_30003 [cl_23591,cl_29805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23591 v h) (hints_cons _ _ _ (der_29805 v h) (by intro d hd; cases hd)))
def cl_30004 : CNF.NClause := [(18,true),(7,true),(28,false),(73,true),(10,false)]
theorem der_30004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30004 :=
  CNF.rup_sound cl_30004 [cl_23592,cl_30003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23592 v h) (hints_cons _ _ _ (der_30003 v h) (by intro d hd; cases hd)))
def cl_30005 : CNF.NClause := [(73,true),(21,false),(10,false),(28,false),(18,false)]
theorem der_30005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30005 :=
  CNF.rup_sound cl_30005 [cl_23593,cl_23535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23593 v h) (hints_cons _ _ _ (der_23535 v h) (by intro d hd; cases hd)))
def cl_30006 : CNF.NClause := [(73,true),(7,false),(21,false),(10,false),(18,false)]
theorem der_30006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30006 :=
  CNF.rup_sound cl_30006 [cl_23595,cl_29972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23595 v h) (hints_cons _ _ _ (der_29972 v h) (by intro d hd; cases hd)))
def cl_30007 : CNF.NClause := [(90,true),(11,false),(22,false),(19,false),(28,false)]
theorem der_30007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30007 :=
  CNF.rup_sound cl_30007 [cl_15345,cl_23209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15345 v h) (hints_cons _ _ _ (der_23209 v h) (by intro d hd; cases hd)))
def cl_30008 : CNF.NClause := [(1,false),(13,false),(71,true),(20,false),(19,false)]
theorem der_30008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30008 :=
  CNF.rup_sound cl_30008 [cl_23600,cl_23599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23600 v h) (hints_cons _ _ _ (der_23599 v h) (by intro d hd; cases hd)))
def cl_30009 : CNF.NClause := [(63,false),(9,true),(4,true),(14,true),(24,true)]
theorem der_30009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30009 :=
  CNF.rup_sound cl_30009 [cl_15040,cl_23214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15040 v h) (hints_cons _ _ _ (der_23214 v h) (by intro d hd; cases hd)))
def cl_30010 : CNF.NClause := [(21,true),(8,false),(14,true),(2,false),(79,true)]
theorem der_30010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30010 :=
  CNF.rup_sound cl_30010 [cl_23606,cl_29819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23606 v h) (hints_cons _ _ _ (der_29819 v h) (by intro d hd; cases hd)))
def cl_30011 : CNF.NClause := [(29,false),(5,false),(14,true),(86,true),(1,false)]
theorem der_30011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30011 :=
  CNF.rup_sound cl_30011 [cl_23607,cl_29827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23607 v h) (hints_cons _ _ _ (der_29827 v h) (by intro d hd; cases hd)))
def cl_30014 : CNF.NClause := [(6,false),(28,true),(70,true),(14,true),(3,false)]
theorem der_30014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30014 :=
  CNF.rup_sound cl_30014 [cl_23614,cl_23613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23614 v h) (hints_cons _ _ _ (der_23613 v h) (by intro d hd; cases hd)))
def cl_30015 : CNF.NClause := [(65,false),(23,true),(18,true),(3,true),(8,true)]
theorem der_30015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30015 :=
  CNF.rup_sound cl_30015 [cl_15106,cl_23277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15106 v h) (hints_cons _ _ _ (der_23277 v h) (by intro d hd; cases hd)))
def cl_30016 : CNF.NClause := [(84,true),(2,true),(5,false),(13,false),(16,false)]
theorem der_30016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30016 :=
  CNF.rup_sound cl_30016 [cl_23619,cl_23617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23619 v h) (hints_cons _ _ _ (der_23617 v h) (by intro d hd; cases hd)))
def cl_30017 : CNF.NClause := [(28,true),(84,true),(2,true),(5,false),(13,false)]
theorem der_30017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30017 :=
  CNF.rup_sound cl_30017 [cl_23620,cl_30016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23620 v h) (hints_cons _ _ _ (der_30016 v h) (by intro d hd; cases hd)))
def cl_30018 : CNF.NClause := [(71,true),(13,false),(26,false),(19,false),(7,true)]
theorem der_30018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30018 :=
  CNF.rup_sound cl_30018 [cl_23622,cl_23621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23622 v h) (hints_cons _ _ _ (der_23621 v h) (by intro d hd; cases hd)))
def cl_30020 : CNF.NClause := [(71,true),(19,false),(1,true),(13,false),(7,true)]
theorem der_30020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30020 :=
  CNF.rup_sound cl_30020 [cl_23624,cl_30018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23624 v h) (hints_cons _ _ _ (der_30018 v h) (by intro d hd; cases hd)))
def cl_30021 : CNF.NClause := [(84,true),(28,true),(5,false),(16,true),(13,false)]
theorem der_30021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30021 :=
  CNF.rup_sound cl_30021 [cl_23628,cl_23627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23628 v h) (hints_cons _ _ _ (der_23627 v h) (by intro d hd; cases hd)))
def cl_30022 : CNF.NClause := [(2,true),(5,false),(24,false),(13,false),(84,true)]
theorem der_30022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30022 :=
  CNF.rup_sound cl_30022 [cl_23629,cl_23618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23629 v h) (hints_cons _ _ _ (der_23618 v h) (by intro d hd; cases hd)))
def cl_30024 : CNF.NClause := [(88,true),(13,false),(29,true),(9,false),(17,true)]
theorem der_30024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30024 :=
  CNF.rup_sound cl_30024 [cl_15311,cl_29946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15311 v h) (hints_cons _ _ _ (der_29946 v h) (by intro d hd; cases hd)))
def cl_30025 : CNF.NClause := [(20,false),(1,false),(13,false),(71,true),(7,false)]
theorem der_30025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30025 :=
  CNF.rup_sound cl_30025 [cl_23631,cl_30008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23631 v h) (hints_cons _ _ _ (der_30008 v h) (by intro d hd; cases hd)))
def cl_30026 : CNF.NClause := [(16,true),(9,false),(75,true),(10,false),(22,false)]
theorem der_30026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30026 :=
  CNF.rup_sound cl_30026 [cl_23634,cl_29980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23634 v h) (hints_cons _ _ _ (der_29980 v h) (by intro d hd; cases hd)))
def cl_30027 : CNF.NClause := [(69,true),(18,true),(20,false),(11,false),(9,false)]
theorem der_30027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30027 :=
  CNF.rup_sound cl_30027 [cl_23635,cl_23584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23635 v h) (hints_cons _ _ _ (der_23584 v h) (by intro d hd; cases hd)))
def cl_30029 : CNF.NClause := [(9,false),(10,false),(26,false),(75,true),(16,true)]
theorem der_30029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30029 :=
  CNF.rup_sound cl_30029 [cl_23637,cl_30026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23637 v h) (hints_cons _ _ _ (der_30026 v h) (by intro d hd; cases hd)))
def cl_30031 : CNF.NClause := [(79,true),(21,true),(2,true),(26,false),(15,false)]
theorem der_30031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30031 :=
  CNF.rup_sound cl_30031 [cl_23639,cl_29816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23639 v h) (hints_cons _ _ _ (der_29816 v h) (by intro d hd; cases hd)))
def cl_30032 : CNF.NClause := [(26,true),(14,false),(15,false),(79,true),(8,false)]
theorem der_30032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30032 :=
  CNF.rup_sound cl_30032 [cl_23641,cl_23522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23641 v h) (hints_cons _ _ _ (der_23522 v h) (by intro d hd; cases hd)))
def cl_30033 : CNF.NClause := [(85,true),(12,true),(3,false),(21,true),(5,false)]
theorem der_30033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30033 :=
  CNF.rup_sound cl_30033 [cl_23645,cl_23644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23645 v h) (hints_cons _ _ _ (der_23644 v h) (by intro d hd; cases hd)))
def cl_30034 : CNF.NClause := [(21,true),(7,true),(73,true),(10,false),(4,false)]
theorem der_30034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30034 :=
  CNF.rup_sound cl_30034 [cl_23646,cl_30002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23646 v h) (hints_cons _ _ _ (der_30002 v h) (by intro d hd; cases hd)))
def cl_30035 : CNF.NClause := [(7,true),(73,true),(10,false),(28,false),(18,false)]
theorem der_30035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30035 :=
  CNF.rup_sound cl_30035 [cl_23647,cl_30005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23647 v h) (hints_cons _ _ _ (der_30005 v h) (by intro d hd; cases hd)))
def cl_30036 : CNF.NClause := [(3,false),(21,true),(19,false),(5,false),(85,true)]
theorem der_30036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30036 :=
  CNF.rup_sound cl_30036 [cl_23649,cl_23648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23649 v h) (hints_cons _ _ _ (der_23648 v h) (by intro d hd; cases hd)))
def cl_30037 : CNF.NClause := [(88,true),(21,true),(9,true),(13,false),(29,false)]
theorem der_30037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30037 :=
  CNF.rup_sound cl_30037 [cl_15296,cl_23261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15296 v h) (hints_cons _ _ _ (der_23261 v h) (by intro d hd; cases hd)))
def cl_30038 : CNF.NClause := [(88,true),(21,true),(29,false),(17,false),(13,true)]
theorem der_30038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30038 :=
  CNF.rup_sound cl_30038 [cl_15294,cl_23260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15294 v h) (hints_cons _ _ _ (der_23260 v h) (by intro d hd; cases hd)))
def cl_30039 : CNF.NClause := [(79,true),(21,true),(15,false),(26,false),(8,false)]
theorem der_30039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30039 :=
  CNF.rup_sound cl_30039 [cl_23652,cl_29818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23652 v h) (hints_cons _ _ _ (der_29818 v h) (by intro d hd; cases hd)))
def cl_30040 : CNF.NClause := [(3,false),(21,true),(5,false),(27,false),(85,true)]
theorem der_30040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30040 :=
  CNF.rup_sound cl_30040 [cl_23653,cl_30036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23653 v h) (hints_cons _ _ _ (der_30036 v h) (by intro d hd; cases hd)))
def cl_30042 : CNF.NClause := [(65,false),(8,true),(18,true),(3,true),(13,true)]
theorem der_30042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30042 :=
  CNF.rup_sound cl_30042 [cl_15094,cl_23277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15094 v h) (hints_cons _ _ _ (der_23277 v h) (by intro d hd; cases hd)))
def cl_30045 : CNF.NClause := [(61,false),(36,false),(37,false),(38,false),(113,true)]
theorem der_30045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30045 :=
  CNF.rup_sound cl_30045 [cl_23676,cl_23673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23676 v h) (hints_cons _ _ _ (der_23673 v h) (by intro d hd; cases hd)))
def cl_30046 : CNF.NClause := [(61,false),(36,false),(37,false),(38,true),(113,true)]
theorem der_30046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30046 :=
  CNF.rup_sound cl_30046 [cl_23677,cl_23670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23677 v h) (hints_cons _ _ _ (der_23670 v h) (by intro d hd; cases hd)))
def cl_30047 : CNF.NClause := [(72,false),(13,true),(10,true),(12,true),(11,true)]
theorem der_30047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30047 :=
  CNF.rup_sound cl_30047 [cl_15190,cl_23358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15190 v h) (hints_cons _ _ _ (der_23358 v h) (by intro d hd; cases hd)))
def cl_30048 : CNF.NClause := [(61,false),(77,true),(72,false),(67,false),(82,true)]
theorem der_30048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30048 :=
  CNF.rup_sound cl_30048 [cl_23686,cl_23684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23686 v h) (hints_cons _ _ _ (der_23684 v h) (by intro d hd; cases hd)))
def cl_30050 : CNF.NClause := [(61,false),(46,false),(49,false),(47,true),(108,true)]
theorem der_30050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30050 :=
  CNF.rup_sound cl_30050 [cl_23695,cl_23694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23695 v h) (hints_cons _ _ _ (der_23694 v h) (by intro d hd; cases hd)))
def cl_30051 : CNF.NClause := [(48,false),(61,false),(46,false),(47,true),(108,true)]
theorem der_30051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30051 :=
  CNF.rup_sound cl_30051 [cl_23696,cl_23694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23696 v h) (hints_cons _ _ _ (der_23694 v h) (by intro d hd; cases hd)))
def cl_30052 : CNF.NClause := [(61,false),(46,false),(47,true),(48,true),(108,true)]
theorem der_30052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30052 :=
  CNF.rup_sound cl_30052 [cl_23697,cl_30050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23697 v h) (hints_cons _ _ _ (der_30050 v h) (by intro d hd; cases hd)))
def cl_30053 : CNF.NClause := [(35,false),(56,false),(45,true),(55,true),(94,true)]
theorem der_30053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30053 :=
  CNF.rup_sound cl_30053 [cl_23702,cl_23701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23702 v h) (hints_cons _ _ _ (der_23701 v h) (by intro d hd; cases hd)))
def cl_30055 : CNF.NClause := [(42,false),(55,false),(34,false),(38,true),(111,true)]
theorem der_30055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30055 :=
  CNF.rup_sound cl_30055 [cl_23723,cl_23722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23723 v h) (hints_cons _ _ _ (der_23722 v h) (by intro d hd; cases hd)))
def cl_30056 : CNF.NClause := [(60,false),(55,false),(34,false),(38,true),(111,true)]
theorem der_30056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30056 :=
  CNF.rup_sound cl_30056 [cl_23724,cl_30055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23724 v h) (hints_cons _ _ _ (der_30055 v h) (by intro d hd; cases hd)))
def cl_30057 : CNF.NClause := [(60,false),(34,false),(38,true),(42,true),(111,true)]
theorem der_30057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30057 :=
  CNF.rup_sound cl_30057 [cl_23726,cl_30056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23726 v h) (hints_cons _ _ _ (der_30056 v h) (by intro d hd; cases hd)))
def cl_30058 : CNF.NClause := [(42,false),(34,false),(46,true),(55,true),(111,true)]
theorem der_30058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30058 :=
  CNF.rup_sound cl_30058 [cl_23728,cl_23720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23728 v h) (hints_cons _ _ _ (der_23720 v h) (by intro d hd; cases hd)))
def cl_30059 : CNF.NClause := [(51,false),(61,false),(52,false),(53,true),(98,true)]
theorem der_30059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30059 :=
  CNF.rup_sound cl_30059 [cl_23731,cl_23730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23731 v h) (hints_cons _ _ _ (der_23730 v h) (by intro d hd; cases hd)))
def cl_30060 : CNF.NClause := [(51,false),(55,false),(52,false),(53,true),(98,true)]
theorem der_30060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30060 :=
  CNF.rup_sound cl_30060 [cl_23733,cl_23729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23733 v h) (hints_cons _ _ _ (der_23729 v h) (by intro d hd; cases hd)))
def cl_30061 : CNF.NClause := [(51,false),(54,false),(52,false),(53,true),(98,true)]
theorem der_30061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30061 :=
  CNF.rup_sound cl_30061 [cl_23734,cl_23730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23734 v h) (hints_cons _ _ _ (der_23730 v h) (by intro d hd; cases hd)))
def cl_30062 : CNF.NClause := [(51,false),(52,false),(53,true),(54,true),(98,true)]
theorem der_30062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30062 :=
  CNF.rup_sound cl_30062 [cl_23735,cl_30060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23735 v h) (hints_cons _ _ _ (der_30060 v h) (by intro d hd; cases hd)))
def cl_30063 : CNF.NClause := [(41,false),(34,false),(47,false),(53,true),(106,true)]
theorem der_30063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30063 :=
  CNF.rup_sound cl_30063 [cl_23739,cl_23738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23739 v h) (hints_cons _ _ _ (der_23738 v h) (by intro d hd; cases hd)))
def cl_30064 : CNF.NClause := [(50,false),(42,false),(31,true),(53,true),(121,true)]
theorem der_30064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30064 :=
  CNF.rup_sound cl_30064 [cl_23745,cl_23742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23745 v h) (hints_cons _ _ _ (der_23742 v h) (by intro d hd; cases hd)))
def cl_30065 : CNF.NClause := [(35,false),(37,false),(44,false),(53,true),(109,true)]
theorem der_30065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30065 :=
  CNF.rup_sound cl_30065 [cl_23747,cl_23741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23747 v h) (hints_cons _ _ _ (der_23741 v h) (by intro d hd; cases hd)))
def cl_30066 : CNF.NClause := [(41,false),(34,false),(40,true),(53,true),(106,true)]
theorem der_30066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30066 :=
  CNF.rup_sound cl_30066 [cl_23749,cl_23748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23749 v h) (hints_cons _ _ _ (der_23748 v h) (by intro d hd; cases hd)))
def cl_30067 : CNF.NClause := [(41,false),(57,false),(34,false),(53,true),(106,true)]
theorem der_30067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30067 :=
  CNF.rup_sound cl_30067 [cl_23750,cl_23748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23750 v h) (hints_cons _ _ _ (der_23748 v h) (by intro d hd; cases hd)))
def cl_30068 : CNF.NClause := [(41,false),(40,false),(34,false),(53,true),(106,true)]
theorem der_30068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30068 :=
  CNF.rup_sound cl_30068 [cl_23751,cl_23738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23751 v h) (hints_cons _ _ _ (der_23738 v h) (by intro d hd; cases hd)))
def cl_30069 : CNF.NClause := [(32,false),(36,false),(45,false),(53,true),(117,true)]
theorem der_30069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30069 :=
  CNF.rup_sound cl_30069 [cl_23753,cl_23740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23753 v h) (hints_cons _ _ _ (der_23740 v h) (by intro d hd; cases hd)))
def cl_30070 : CNF.NClause := [(32,false),(36,false),(49,true),(53,true),(117,true)]
theorem der_30070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30070 :=
  CNF.rup_sound cl_30070 [cl_23755,cl_23754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23755 v h) (hints_cons _ _ _ (der_23754 v h) (by intro d hd; cases hd)))
def cl_30072 : CNF.NClause := [(51,false),(61,false),(54,false),(53,true),(98,true)]
theorem der_30072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30072 :=
  CNF.rup_sound cl_30072 [cl_23758,cl_23756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23758 v h) (hints_cons _ _ _ (der_23756 v h) (by intro d hd; cases hd)))
def cl_30074 : CNF.NClause := [(59,false),(42,false),(31,true),(53,true),(121,true)]
theorem der_30074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30074 :=
  CNF.rup_sound cl_30074 [cl_23761,cl_23760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23761 v h) (hints_cons _ _ _ (der_23760 v h) (by intro d hd; cases hd)))
def cl_30075 : CNF.NClause := [(42,false),(39,false),(31,true),(53,true),(121,true)]
theorem der_30075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30075 :=
  CNF.rup_sound cl_30075 [cl_23762,cl_30074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23762 v h) (hints_cons _ _ _ (der_30074 v h) (by intro d hd; cases hd)))
def cl_30076 : CNF.NClause := [(51,false),(54,false),(55,false),(53,true),(98,true)]
theorem der_30076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30076 :=
  CNF.rup_sound cl_30076 [cl_23764,cl_30072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23764 v h) (hints_cons _ _ _ (der_30072 v h) (by intro d hd; cases hd)))
def cl_30077 : CNF.NClause := [(51,false),(55,false),(53,true),(54,true),(98,true)]
theorem der_30077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30077 :=
  CNF.rup_sound cl_30077 [cl_23765,cl_30060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23765 v h) (hints_cons _ _ _ (der_30060 v h) (by intro d hd; cases hd)))
def cl_30078 : CNF.NClause := [(51,false),(54,false),(53,true),(55,true),(98,true)]
theorem der_30078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30078 :=
  CNF.rup_sound cl_30078 [cl_23766,cl_30072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23766 v h) (hints_cons _ _ _ (der_30072 v h) (by intro d hd; cases hd)))
def cl_30079 : CNF.NClause := [(35,false),(37,false),(53,true),(46,true),(109,true)]
theorem der_30079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30079 :=
  CNF.rup_sound cl_30079 [cl_23768,cl_23767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23768 v h) (hints_cons _ _ _ (der_23767 v h) (by intro d hd; cases hd)))
def cl_30080 : CNF.NClause := [(56,true),(38,true),(33,false),(43,false),(95,true)]
theorem der_30080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30080 :=
  CNF.rup_sound cl_30080 [cl_23770,cl_23274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23770 v h) (hints_cons _ _ _ (der_23274 v h) (by intro d hd; cases hd)))
def cl_30081 : CNF.NClause := [(64,false),(17,true),(22,true),(7,true),(12,true)]
theorem der_30081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30081 :=
  CNF.rup_sound cl_30081 [cl_15077,cl_23353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15077 v h) (hints_cons _ _ _ (der_23353 v h) (by intro d hd; cases hd)))
def cl_30082 : CNF.NClause := [(64,false),(17,true),(2,true),(22,true),(7,true)]
theorem der_30082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30082 :=
  CNF.rup_sound cl_30082 [cl_15074,cl_23353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15074 v h) (hints_cons _ _ _ (der_23353 v h) (by intro d hd; cases hd)))
def cl_30084 : CNF.NClause := [(38,false),(56,false),(33,false),(43,false),(95,true)]
theorem der_30084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30084 :=
  CNF.rup_sound cl_30084 [cl_23778,cl_23777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23778 v h) (hints_cons _ _ _ (der_23777 v h) (by intro d hd; cases hd)))
def cl_30085 : CNF.NClause := [(48,false),(38,false),(33,false),(43,false),(95,true)]
theorem der_30085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30085 :=
  CNF.rup_sound cl_30085 [cl_23779,cl_23777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23779 v h) (hints_cons _ _ _ (der_23777 v h) (by intro d hd; cases hd)))
def cl_30087 : CNF.NClause := [(48,false),(33,false),(43,false),(53,false),(95,true)]
theorem der_30087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30087 :=
  CNF.rup_sound cl_30087 [cl_23782,cl_30085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23782 v h) (hints_cons _ _ _ (der_30085 v h) (by intro d hd; cases hd)))
def cl_30088 : CNF.NClause := [(38,true),(33,false),(43,false),(53,false),(95,true)]
theorem der_30088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30088 :=
  CNF.rup_sound cl_30088 [cl_23784,cl_30080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23784 v h) (hints_cons _ _ _ (der_30080 v h) (by intro d hd; cases hd)))
def cl_30089 : CNF.NClause := [(56,false),(38,true),(33,false),(53,false),(95,true)]
theorem der_30089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30089 :=
  CNF.rup_sound cl_30089 [cl_23785,cl_30088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23785 v h) (hints_cons _ _ _ (der_30088 v h) (by intro d hd; cases hd)))
def cl_30090 : CNF.NClause := [(48,false),(33,false),(43,false),(53,true),(95,true)]
theorem der_30090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30090 :=
  CNF.rup_sound cl_30090 [cl_23786,cl_30085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23786 v h) (hints_cons _ _ _ (der_30085 v h) (by intro d hd; cases hd)))
def cl_30091 : CNF.NClause := [(38,true),(33,false),(43,false),(53,true),(95,true)]
theorem der_30091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30091 :=
  CNF.rup_sound cl_30091 [cl_23788,cl_30090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23788 v h) (hints_cons _ _ _ (der_30090 v h) (by intro d hd; cases hd)))
def cl_30093 : CNF.NClause := [(51,false),(61,false),(55,false),(52,true),(98,true)]
theorem der_30093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30093 :=
  CNF.rup_sound cl_30093 [cl_23794,cl_23793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23794 v h) (hints_cons _ _ _ (der_23793 v h) (by intro d hd; cases hd)))
def cl_30094 : CNF.NClause := [(51,false),(61,false),(54,false),(52,true),(98,true)]
theorem der_30094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30094 :=
  CNF.rup_sound cl_30094 [cl_23795,cl_30072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23795 v h) (hints_cons _ _ _ (der_30072 v h) (by intro d hd; cases hd)))
def cl_30095 : CNF.NClause := [(51,false),(61,false),(54,true),(52,true),(98,true)]
theorem der_30095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30095 :=
  CNF.rup_sound cl_30095 [cl_23796,cl_30093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23796 v h) (hints_cons _ _ _ (der_30093 v h) (by intro d hd; cases hd)))
def cl_30096 : CNF.NClause := [(51,false),(54,false),(55,false),(52,true),(98,true)]
theorem der_30096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30096 :=
  CNF.rup_sound cl_30096 [cl_23797,cl_30076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23797 v h) (hints_cons _ _ _ (der_30076 v h) (by intro d hd; cases hd)))
def cl_30097 : CNF.NClause := [(48,false),(61,false),(46,false),(49,true),(108,true)]
theorem der_30097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30097 :=
  CNF.rup_sound cl_30097 [cl_23804,cl_30051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23804 v h) (hints_cons _ _ _ (der_30051 v h) (by intro d hd; cases hd)))
def cl_30099 : CNF.NClause := [(41,false),(57,false),(40,false),(34,false),(106,true)]
theorem der_30099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30099 :=
  CNF.rup_sound cl_30099 [cl_23820,cl_30067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23820 v h) (hints_cons _ _ _ (der_30067 v h) (by intro d hd; cases hd)))
def cl_30100 : CNF.NClause := [(35,false),(59,false),(38,false),(49,true),(104,true)]
theorem der_30100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30100 :=
  CNF.rup_sound cl_30100 [cl_23823,cl_23821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23823 v h) (hints_cons _ _ _ (der_23821 v h) (by intro d hd; cases hd)))
def cl_30101 : CNF.NClause := [(35,false),(38,false),(52,false),(49,true),(104,true)]
theorem der_30101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30101 :=
  CNF.rup_sound cl_30101 [cl_23825,cl_23821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23825 v h) (hints_cons _ _ _ (der_23821 v h) (by intro d hd; cases hd)))
def cl_30102 : CNF.NClause := [(35,false),(38,false),(49,false),(41,true),(104,true)]
theorem der_30102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30102 :=
  CNF.rup_sound cl_30102 [cl_23826,cl_23824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23826 v h) (hints_cons _ _ _ (der_23824 v h) (by intro d hd; cases hd)))
def cl_30103 : CNF.NClause := [(35,false),(38,false),(49,true),(52,true),(104,true)]
theorem der_30103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30103 :=
  CNF.rup_sound cl_30103 [cl_23827,cl_30100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23827 v h) (hints_cons _ _ _ (der_30100 v h) (by intro d hd; cases hd)))
def cl_30104 : CNF.NClause := [(35,false),(59,false),(49,true),(52,true),(104,true)]
theorem der_30104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30104 :=
  CNF.rup_sound cl_30104 [cl_23831,cl_30103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23831 v h) (hints_cons _ _ _ (der_30103 v h) (by intro d hd; cases hd)))
def cl_30105 : CNF.NClause := [(35,false),(49,false),(38,true),(59,true),(104,true)]
theorem der_30105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30105 :=
  CNF.rup_sound cl_30105 [cl_23836,cl_23835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23836 v h) (hints_cons _ _ _ (der_23835 v h) (by intro d hd; cases hd)))
def cl_30106 : CNF.NClause := [(41,false),(35,false),(49,true),(52,true),(104,true)]
theorem der_30106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30106 :=
  CNF.rup_sound cl_30106 [cl_23837,cl_30104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23837 v h) (hints_cons _ _ _ (der_30104 v h) (by intro d hd; cases hd)))
def cl_30107 : CNF.NClause := [(41,false),(57,false),(34,false),(47,false),(106,true)]
theorem der_30107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30107 :=
  CNF.rup_sound cl_30107 [cl_23839,cl_30067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23839 v h) (hints_cons _ _ _ (der_30067 v h) (by intro d hd; cases hd)))
def cl_30108 : CNF.NClause := [(51,false),(55,false),(53,false),(52,true),(98,true)]
theorem der_30108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30108 :=
  CNF.rup_sound cl_30108 [cl_23843,cl_30093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23843 v h) (hints_cons _ _ _ (der_30093 v h) (by intro d hd; cases hd)))
def cl_30109 : CNF.NClause := [(51,false),(54,false),(55,true),(52,true),(98,true)]
theorem der_30109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30109 :=
  CNF.rup_sound cl_30109 [cl_23844,cl_30094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23844 v h) (hints_cons _ _ _ (der_30094 v h) (by intro d hd; cases hd)))
def cl_30110 : CNF.NClause := [(51,false),(54,true),(52,true),(53,false),(98,true)]
theorem der_30110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30110 :=
  CNF.rup_sound cl_30110 [cl_23845,cl_30095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23845 v h) (hints_cons _ _ _ (der_30095 v h) (by intro d hd; cases hd)))
def cl_30111 : CNF.NClause := [(51,false),(42,false),(33,false),(49,true),(100,true)]
theorem der_30111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30111 :=
  CNF.rup_sound cl_30111 [cl_23846,cl_23814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23846 v h) (hints_cons _ _ _ (der_23814 v h) (by intro d hd; cases hd)))
def cl_30113 : CNF.NClause := [(50,false),(46,false),(49,true),(47,true),(108,true)]
theorem der_30113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30113 :=
  CNF.rup_sound cl_30113 [cl_23855,cl_23817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23855 v h) (hints_cons _ _ _ (der_23817 v h) (by intro d hd; cases hd)))
def cl_30114 : CNF.NClause := [(48,false),(50,false),(46,false),(49,true),(108,true)]
theorem der_30114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30114 :=
  CNF.rup_sound cl_30114 [cl_23861,cl_30113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23861 v h) (hints_cons _ _ _ (der_30113 v h) (by intro d hd; cases hd)))
def cl_30115 : CNF.NClause := [(36,false),(47,false),(33,false),(44,true),(115,true)]
theorem der_30115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30115 :=
  CNF.rup_sound cl_30115 [cl_23869,cl_23868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23869 v h) (hints_cons _ _ _ (der_23868 v h) (by intro d hd; cases hd)))
def cl_30116 : CNF.NClause := [(36,false),(47,true),(33,false),(55,true),(115,true)]
theorem der_30116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30116 :=
  CNF.rup_sound cl_30116 [cl_23870,cl_23867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23870 v h) (hints_cons _ _ _ (der_23867 v h) (by intro d hd; cases hd)))
def cl_30117 : CNF.NClause := [(39,false),(34,false),(49,true),(54,true),(96,true)]
theorem der_30117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30117 :=
  CNF.rup_sound cl_30117 [cl_23871,cl_23864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23871 v h) (hints_cons _ _ _ (der_23864 v h) (by intro d hd; cases hd)))
def cl_30119 : CNF.NClause := [(35,false),(58,false),(37,false),(53,true),(109,true)]
theorem der_30119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30119 :=
  CNF.rup_sound cl_30119 [cl_23873,cl_23767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23873 v h) (hints_cons _ _ _ (der_23767 v h) (by intro d hd; cases hd)))
def cl_30120 : CNF.NClause := [(35,false),(37,false),(53,true),(58,true),(109,true)]
theorem der_30120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30120 :=
  CNF.rup_sound cl_30120 [cl_23875,cl_30065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23875 v h) (hints_cons _ _ _ (der_30065 v h) (by intro d hd; cases hd)))
def cl_30121 : CNF.NClause := [(41,false),(61,false),(44,true),(43,true),(103,true)]
theorem der_30121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30121 :=
  CNF.rup_sound cl_30121 [cl_23880,cl_23879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23880 v h) (hints_cons _ _ _ (der_23879 v h) (by intro d hd; cases hd)))
def cl_30122 : CNF.NClause := [(41,false),(61,false),(45,false),(44,true),(103,true)]
theorem der_30122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30122 :=
  CNF.rup_sound cl_30122 [cl_23882,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23882 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_30123 : CNF.NClause := [(41,false),(45,false),(44,true),(42,true),(103,true)]
theorem der_30123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30123 :=
  CNF.rup_sound cl_30123 [cl_23884,cl_30122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23884 v h) (hints_cons _ _ _ (der_30122 v h) (by intro d hd; cases hd)))
def cl_30124 : CNF.NClause := [(35,false),(37,false),(44,true),(46,true),(109,true)]
theorem der_30124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30124 :=
  CNF.rup_sound cl_30124 [cl_23886,cl_23828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23886 v h) (hints_cons _ _ _ (der_23828 v h) (by intro d hd; cases hd)))
def cl_30125 : CNF.NClause := [(32,false),(50,false),(38,false),(51,true),(102,true)]
theorem der_30125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30125 :=
  CNF.rup_sound cl_30125 [cl_23897,cl_23893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23897 v h) (hints_cons _ _ _ (der_23893 v h) (by intro d hd; cases hd)))
def cl_30126 : CNF.NClause := [(32,false),(38,false),(44,true),(50,true),(102,true)]
theorem der_30126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30126 :=
  CNF.rup_sound cl_30126 [cl_23898,cl_23894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23898 v h) (hints_cons _ _ _ (der_23894 v h) (by intro d hd; cases hd)))
def cl_30127 : CNF.NClause := [(32,false),(36,false),(49,true),(60,true),(117,true)]
theorem der_30127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30127 :=
  CNF.rup_sound cl_30127 [cl_23901,cl_23815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23901 v h) (hints_cons _ _ _ (der_23815 v h) (by intro d hd; cases hd)))
def cl_30128 : CNF.NClause := [(32,false),(36,false),(45,true),(49,true),(117,true)]
theorem der_30128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30128 :=
  CNF.rup_sound cl_30128 [cl_23902,cl_23815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23902 v h) (hints_cons _ _ _ (der_23815 v h) (by intro d hd; cases hd)))
def cl_30129 : CNF.NClause := [(32,false),(36,false),(45,false),(49,true),(117,true)]
theorem der_30129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30129 :=
  CNF.rup_sound cl_30129 [cl_23904,cl_30127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23904 v h) (hints_cons _ _ _ (der_30127 v h) (by intro d hd; cases hd)))
def cl_30130 : CNF.NClause := [(32,false),(50,false),(44,false),(51,true),(102,true)]
theorem der_30130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30130 :=
  CNF.rup_sound cl_30130 [cl_23914,cl_30125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23914 v h) (hints_cons _ _ _ (der_30125 v h) (by intro d hd; cases hd)))
def cl_30131 : CNF.NClause := [(32,false),(50,false),(38,true),(44,true),(102,true)]
theorem der_30131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30131 :=
  CNF.rup_sound cl_30131 [cl_23915,cl_23907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23915 v h) (hints_cons _ _ _ (der_23907 v h) (by intro d hd; cases hd)))
def cl_30132 : CNF.NClause := [(32,false),(44,false),(38,true),(51,true),(102,true)]
theorem der_30132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30132 :=
  CNF.rup_sound cl_30132 [cl_23916,cl_30130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23916 v h) (hints_cons _ _ _ (der_30130 v h) (by intro d hd; cases hd)))
def cl_30133 : CNF.NClause := [(21,true),(2,false),(26,false),(79,true),(14,true)]
theorem der_30133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30133 :=
  CNF.rup_sound cl_30133 [cl_23967,cl_29818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23967 v h) (hints_cons _ _ _ (der_29818 v h) (by intro d hd; cases hd)))
def cl_30134 : CNF.NClause := [(79,true),(26,true),(15,false),(14,false),(21,false)]
theorem der_30134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30134 :=
  CNF.rup_sound cl_30134 [cl_23968,cl_23522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23968 v h) (hints_cons _ _ _ (der_23522 v h) (by intro d hd; cases hd)))
def cl_30135 : CNF.NClause := [(2,false),(15,false),(8,true),(79,true),(21,false)]
theorem der_30135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30135 :=
  CNF.rup_sound cl_30135 [cl_23969,cl_23961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23969 v h) (hints_cons _ _ _ (der_23961 v h) (by intro d hd; cases hd)))
def cl_30136 : CNF.NClause := [(14,false),(79,true),(2,false),(8,true),(21,false)]
theorem der_30136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30136 :=
  CNF.rup_sound cl_30136 [cl_23970,cl_23962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23970 v h) (hints_cons _ _ _ (der_23962 v h) (by intro d hd; cases hd)))
def cl_30137 : CNF.NClause := [(8,true),(15,true),(2,false),(21,false),(79,true)]
theorem der_30137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30137 :=
  CNF.rup_sound cl_30137 [cl_23971,cl_30136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23971 v h) (hints_cons _ _ _ (der_30136 v h) (by intro d hd; cases hd)))
def cl_30138 : CNF.NClause := [(26,true),(79,true),(15,false),(14,false),(21,true)]
theorem der_30138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30138 :=
  CNF.rup_sound cl_30138 [cl_23972,cl_30032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23972 v h) (hints_cons _ _ _ (der_30032 v h) (by intro d hd; cases hd)))
def cl_30139 : CNF.NClause := [(26,true),(2,false),(8,true),(15,false),(79,true)]
theorem der_30139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30139 :=
  CNF.rup_sound cl_30139 [cl_23973,cl_30135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23973 v h) (hints_cons _ _ _ (der_30135 v h) (by intro d hd; cases hd)))
def cl_30140 : CNF.NClause := [(79,true),(14,false),(8,true),(15,true),(2,false)]
theorem der_30140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30140 :=
  CNF.rup_sound cl_30140 [cl_23974,cl_30136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23974 v h) (hints_cons _ _ _ (der_30136 v h) (by intro d hd; cases hd)))
def cl_30141 : CNF.NClause := [(29,false),(68,true),(16,true),(4,false),(20,false)]
theorem der_30141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30141 :=
  CNF.rup_sound cl_30141 [cl_23975,cl_29981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23975 v h) (hints_cons _ _ _ (der_29981 v h) (by intro d hd; cases hd)))
def cl_30142 : CNF.NClause := [(68,true),(29,false),(20,true),(16,true),(4,false)]
theorem der_30142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30142 :=
  CNF.rup_sound cl_30142 [cl_23977,cl_29981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23977 v h) (hints_cons _ _ _ (der_29981 v h) (by intro d hd; cases hd)))
def cl_30143 : CNF.NClause := [(68,true),(12,false),(20,false),(4,false),(8,true)]
theorem der_30143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30143 :=
  CNF.rup_sound cl_30143 [cl_23979,cl_23978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23979 v h) (hints_cons _ _ _ (der_23978 v h) (by intro d hd; cases hd)))
def cl_30144 : CNF.NClause := [(16,false),(68,true),(12,false),(8,true),(4,false)]
theorem der_30144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30144 :=
  CNF.rup_sound cl_30144 [cl_23980,cl_23978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23980 v h) (hints_cons _ _ _ (der_23978 v h) (by intro d hd; cases hd)))
def cl_30145 : CNF.NClause := [(68,true),(29,true),(12,false),(4,false),(8,true)]
theorem der_30145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30145 :=
  CNF.rup_sound cl_30145 [cl_23981,cl_30144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23981 v h) (hints_cons _ _ _ (der_30144 v h) (by intro d hd; cases hd)))
def cl_30146 : CNF.NClause := [(68,true),(8,true),(20,false),(29,false),(12,false)]
theorem der_30146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30146 :=
  CNF.rup_sound cl_30146 [cl_23983,cl_23982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23983 v h) (hints_cons _ _ _ (der_23982 v h) (by intro d hd; cases hd)))
def cl_30147 : CNF.NClause := [(68,true),(29,false),(8,true),(20,false),(16,true)]
theorem der_30147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30147 :=
  CNF.rup_sound cl_30147 [cl_23984,cl_30146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23984 v h) (hints_cons _ _ _ (der_30146 v h) (by intro d hd; cases hd)))
def cl_30148 : CNF.NClause := [(68,true),(8,true),(29,false),(12,false),(16,false)]
theorem der_30148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30148 :=
  CNF.rup_sound cl_30148 [cl_23985,cl_23976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23985 v h) (hints_cons _ _ _ (der_23976 v h) (by intro d hd; cases hd)))
def cl_30149 : CNF.NClause := [(12,false),(29,false),(4,true),(68,true),(8,true)]
theorem der_30149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30149 :=
  CNF.rup_sound cl_30149 [cl_23986,cl_30148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23986 v h) (hints_cons _ _ _ (der_30148 v h) (by intro d hd; cases hd)))
def cl_30150 : CNF.NClause := [(68,true),(8,true),(20,false),(12,false),(16,false)]
theorem der_30150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30150 :=
  CNF.rup_sound cl_30150 [cl_23987,cl_30146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23987 v h) (hints_cons _ _ _ (der_30146 v h) (by intro d hd; cases hd)))
def cl_30151 : CNF.NClause := [(68,true),(29,true),(8,true),(20,false),(12,false)]
theorem der_30151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30151 :=
  CNF.rup_sound cl_30151 [cl_23988,cl_30150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23988 v h) (hints_cons _ _ _ (der_30150 v h) (by intro d hd; cases hd)))
def cl_30152 : CNF.NClause := [(68,true),(29,true),(8,true),(12,false),(16,false)]
theorem der_30152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30152 :=
  CNF.rup_sound cl_30152 [cl_23989,cl_30145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23989 v h) (hints_cons _ _ _ (der_30145 v h) (by intro d hd; cases hd)))
def cl_30154 : CNF.NClause := [(1,false),(27,true),(24,false),(76,true),(8,true)]
theorem der_30154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30154 :=
  CNF.rup_sound cl_30154 [cl_23994,cl_23993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23994 v h) (hints_cons _ _ _ (der_23993 v h) (by intro d hd; cases hd)))
def cl_30155 : CNF.NClause := [(76,true),(8,true),(27,true),(17,false),(1,false)]
theorem der_30155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30155 :=
  CNF.rup_sound cl_30155 [cl_23996,cl_23995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23996 v h) (hints_cons _ _ _ (der_23995 v h) (by intro d hd; cases hd)))
def cl_30156 : CNF.NClause := [(76,true),(8,true),(27,true),(10,false),(1,false)]
theorem der_30156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30156 :=
  CNF.rup_sound cl_30156 [cl_23997,cl_30155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23997 v h) (hints_cons _ _ _ (der_30155 v h) (by intro d hd; cases hd)))
def cl_30158 : CNF.NClause := [(68,true),(8,true),(20,false),(29,false),(16,false)]
theorem der_30158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30158 :=
  CNF.rup_sound cl_30158 [cl_23999,cl_30150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23999 v h) (hints_cons _ _ _ (der_30150 v h) (by intro d hd; cases hd)))
def cl_30159 : CNF.NClause := [(68,true),(8,true),(4,true),(20,false),(16,false)]
theorem der_30159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30159 :=
  CNF.rup_sound cl_30159 [cl_24000,cl_30158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24000 v h) (hints_cons _ _ _ (der_30158 v h) (by intro d hd; cases hd)))
def cl_30160 : CNF.NClause := [(26,true),(79,true),(8,true),(21,false),(15,false)]
theorem der_30160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30160 :=
  CNF.rup_sound cl_30160 [cl_24001,cl_30135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24001 v h) (hints_cons _ _ _ (der_30135 v h) (by intro d hd; cases hd)))
def cl_30162 : CNF.NClause := [(74,true),(2,false),(23,false),(29,false),(6,true)]
theorem der_30162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30162 :=
  CNF.rup_sound cl_30162 [cl_24005,cl_24003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24005 v h) (hints_cons _ _ _ (der_24003 v h) (by intro d hd; cases hd)))
def cl_30163 : CNF.NClause := [(29,false),(74,true),(19,false),(6,true),(2,false)]
theorem der_30163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30163 :=
  CNF.rup_sound cl_30163 [cl_24007,cl_24006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24007 v h) (hints_cons _ _ _ (der_24006 v h) (by intro d hd; cases hd)))
def cl_30164 : CNF.NClause := [(29,false),(74,true),(6,true),(10,false),(2,false)]
theorem der_30164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30164 :=
  CNF.rup_sound cl_30164 [cl_24008,cl_30163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24008 v h) (hints_cons _ _ _ (der_30163 v h) (by intro d hd; cases hd)))
def cl_30165 : CNF.NClause := [(74,true),(19,true),(2,false),(29,false),(6,true)]
theorem der_30165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30165 :=
  CNF.rup_sound cl_30165 [cl_24009,cl_30164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24009 v h) (hints_cons _ _ _ (der_30164 v h) (by intro d hd; cases hd)))
def cl_30166 : CNF.NClause := [(74,true),(19,false),(23,false),(6,true),(2,false)]
theorem der_30166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30166 :=
  CNF.rup_sound cl_30166 [cl_24011,cl_24010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24011 v h) (hints_cons _ _ _ (der_24010 v h) (by intro d hd; cases hd)))
def cl_30167 : CNF.NClause := [(10,false),(74,true),(6,true),(23,false),(2,false)]
theorem der_30167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30167 :=
  CNF.rup_sound cl_30167 [cl_24012,cl_30166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24012 v h) (hints_cons _ _ _ (der_30166 v h) (by intro d hd; cases hd)))
def cl_30168 : CNF.NClause := [(74,true),(10,true),(6,true),(23,false),(2,false)]
theorem der_30168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30168 :=
  CNF.rup_sound cl_30168 [cl_24013,cl_30166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24013 v h) (hints_cons _ _ _ (der_30166 v h) (by intro d hd; cases hd)))
def cl_30169 : CNF.NClause := [(10,false),(74,true),(6,true),(19,false),(2,false)]
theorem der_30169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30169 :=
  CNF.rup_sound cl_30169 [cl_24014,cl_24010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24014 v h) (hints_cons _ _ _ (der_24010 v h) (by intro d hd; cases hd)))
def cl_30170 : CNF.NClause := [(10,true),(19,false),(74,true),(6,true),(2,false)]
theorem der_30170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30170 :=
  CNF.rup_sound cl_30170 [cl_24015,cl_30163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24015 v h) (hints_cons _ _ _ (der_30163 v h) (by intro d hd; cases hd)))
def cl_30171 : CNF.NClause := [(74,true),(19,true),(6,true),(10,false),(2,false)]
theorem der_30171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30171 :=
  CNF.rup_sound cl_30171 [cl_24016,cl_30165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24016 v h) (hints_cons _ _ _ (der_30165 v h) (by intro d hd; cases hd)))
def cl_30172 : CNF.NClause := [(28,false),(14,true),(3,false),(70,true),(20,false)]
theorem der_30172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30172 :=
  CNF.rup_sound cl_30172 [cl_24018,cl_29832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24018 v h) (hints_cons _ _ _ (der_29832 v h) (by intro d hd; cases hd)))
def cl_30173 : CNF.NClause := [(28,false),(70,true),(6,true),(3,false),(20,false)]
theorem der_30173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30173 :=
  CNF.rup_sound cl_30173 [cl_24019,cl_30172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24019 v h) (hints_cons _ _ _ (der_30172 v h) (by intro d hd; cases hd)))
def cl_30174 : CNF.NClause := [(14,false),(28,false),(6,true),(70,true),(3,false)]
theorem der_30174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30174 :=
  CNF.rup_sound cl_30174 [cl_24023,cl_24021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24023 v h) (hints_cons _ _ _ (der_24021 v h) (by intro d hd; cases hd)))
def cl_30175 : CNF.NClause := [(6,true),(28,false),(3,false),(17,true),(70,true)]
theorem der_30175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30175 :=
  CNF.rup_sound cl_30175 [cl_24024,cl_30174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24024 v h) (hints_cons _ _ _ (der_30174 v h) (by intro d hd; cases hd)))
def cl_30176 : CNF.NClause := [(14,true),(3,false),(20,false),(70,true),(28,true)]
theorem der_30176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30176 :=
  CNF.rup_sound cl_30176 [cl_24026,cl_29832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24026 v h) (hints_cons _ _ _ (der_29832 v h) (by intro d hd; cases hd)))
def cl_30177 : CNF.NClause := [(14,false),(3,false),(6,true),(70,true),(20,false)]
theorem der_30177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30177 :=
  CNF.rup_sound cl_30177 [cl_24027,cl_24025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24027 v h) (hints_cons _ _ _ (der_24025 v h) (by intro d hd; cases hd)))
def cl_30178 : CNF.NClause := [(6,true),(14,false),(3,false),(70,true),(17,false)]
theorem der_30178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30178 :=
  CNF.rup_sound cl_30178 [cl_24029,cl_30177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24029 v h) (hints_cons _ _ _ (der_30177 v h) (by intro d hd; cases hd)))
def cl_30179 : CNF.NClause := [(28,true),(14,true),(3,false),(70,true),(17,false)]
theorem der_30179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30179 :=
  CNF.rup_sound cl_30179 [cl_24030,cl_30176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24030 v h) (hints_cons _ _ _ (der_30176 v h) (by intro d hd; cases hd)))
def cl_30180 : CNF.NClause := [(14,false),(6,true),(17,true),(70,true),(3,false)]
theorem der_30180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30180 :=
  CNF.rup_sound cl_30180 [cl_24031,cl_30175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24031 v h) (hints_cons _ _ _ (der_30175 v h) (by intro d hd; cases hd)))
def cl_30181 : CNF.NClause := [(78,true),(15,false),(4,false),(27,false),(13,false)]
theorem der_30181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30181 :=
  CNF.rup_sound cl_30181 [cl_24034,cl_24032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24034 v h) (hints_cons _ _ _ (der_24032 v h) (by intro d hd; cases hd)))
def cl_30182 : CNF.NClause := [(27,false),(78,true),(4,false),(6,true),(13,false)]
theorem der_30182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30182 :=
  CNF.rup_sound cl_30182 [cl_24035,cl_30181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24035 v h) (hints_cons _ _ _ (der_30181 v h) (by intro d hd; cases hd)))
def cl_30183 : CNF.NClause := [(13,false),(78,true),(6,true),(4,false),(22,false)]
theorem der_30183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30183 :=
  CNF.rup_sound cl_30183 [cl_24037,cl_24036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24037 v h) (hints_cons _ _ _ (der_24036 v h) (by intro d hd; cases hd)))
def cl_30184 : CNF.NClause := [(78,true),(13,false),(22,true),(15,false),(4,false)]
theorem der_30184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30184 :=
  CNF.rup_sound cl_30184 [cl_24038,cl_30181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24038 v h) (hints_cons _ _ _ (der_30181 v h) (by intro d hd; cases hd)))
def cl_30185 : CNF.NClause := [(78,true),(6,true),(22,true),(4,false),(13,false)]
theorem der_30185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30185 :=
  CNF.rup_sound cl_30185 [cl_24039,cl_30184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24039 v h) (hints_cons _ _ _ (der_30184 v h) (by intro d hd; cases hd)))
def cl_30187 : CNF.NClause := [(29,false),(6,true),(74,true),(10,false),(19,false)]
theorem der_30187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30187 :=
  CNF.rup_sound cl_30187 [cl_24042,cl_24006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24042 v h) (hints_cons _ _ _ (der_24006 v h) (by intro d hd; cases hd)))
def cl_30188 : CNF.NClause := [(74,true),(2,true),(19,true),(10,false),(29,false)]
theorem der_30188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30188 :=
  CNF.rup_sound cl_30188 [cl_24043,cl_24041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24043 v h) (hints_cons _ _ _ (der_24041 v h) (by intro d hd; cases hd)))
def cl_30189 : CNF.NClause := [(74,true),(29,true),(2,true),(10,false),(23,false)]
theorem der_30189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30189 :=
  CNF.rup_sound cl_30189 [cl_24045,cl_24044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24045 v h) (hints_cons _ _ _ (der_24044 v h) (by intro d hd; cases hd)))
def cl_30190 : CNF.NClause := [(10,false),(29,true),(74,true),(2,true),(19,false)]
theorem der_30190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30190 :=
  CNF.rup_sound cl_30190 [cl_24046,cl_30189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24046 v h) (hints_cons _ _ _ (der_30189 v h) (by intro d hd; cases hd)))
def cl_30191 : CNF.NClause := [(78,true),(6,true),(27,false),(13,false),(22,false)]
theorem der_30191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30191 :=
  CNF.rup_sound cl_30191 [cl_24049,cl_24047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24049 v h) (hints_cons _ _ _ (der_24047 v h) (by intro d hd; cases hd)))
def cl_30192 : CNF.NClause := [(78,true),(27,false),(6,true),(4,true),(22,false)]
theorem der_30192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30192 :=
  CNF.rup_sound cl_30192 [cl_24050,cl_24048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24050 v h) (hints_cons _ _ _ (der_24048 v h) (by intro d hd; cases hd)))
def cl_30194 : CNF.NClause := [(78,true),(4,true),(6,true),(15,false),(27,false)]
theorem der_30194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30194 :=
  CNF.rup_sound cl_30194 [cl_24052,cl_24048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24052 v h) (hints_cons _ _ _ (der_24048 v h) (by intro d hd; cases hd)))
def cl_30195 : CNF.NClause := [(78,true),(15,true),(6,true),(27,false),(13,false)]
theorem der_30195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30195 :=
  CNF.rup_sound cl_30195 [cl_24053,cl_30191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24053 v h) (hints_cons _ _ _ (der_30191 v h) (by intro d hd; cases hd)))
def cl_30196 : CNF.NClause := [(22,false),(78,true),(6,true),(15,false),(13,false)]
theorem der_30196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30196 :=
  CNF.rup_sound cl_30196 [cl_24054,cl_24047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24054 v h) (hints_cons _ _ _ (der_24047 v h) (by intro d hd; cases hd)))
def cl_30197 : CNF.NClause := [(78,true),(6,true),(4,true),(15,false),(22,false)]
theorem der_30197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30197 :=
  CNF.rup_sound cl_30197 [cl_24055,cl_30196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24055 v h) (hints_cons _ _ _ (der_30196 v h) (by intro d hd; cases hd)))
def cl_30198 : CNF.NClause := [(78,true),(4,true),(22,false),(13,false),(6,true)]
theorem der_30198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30198 :=
  CNF.rup_sound cl_30198 [cl_24056,cl_30196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24056 v h) (hints_cons _ _ _ (der_30196 v h) (by intro d hd; cases hd)))
def cl_30199 : CNF.NClause := [(27,true),(13,false),(78,true),(6,true),(15,false)]
theorem der_30199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30199 :=
  CNF.rup_sound cl_30199 [cl_24057,cl_30196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24057 v h) (hints_cons _ _ _ (der_30196 v h) (by intro d hd; cases hd)))
def cl_30200 : CNF.NClause := [(29,false),(1,false),(5,true),(86,true),(22,false)]
theorem der_30200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30200 :=
  CNF.rup_sound cl_30200 [cl_24063,cl_29831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24063 v h) (hints_cons _ _ _ (der_29831 v h) (by intro d hd; cases hd)))
def cl_30201 : CNF.NClause := [(29,false),(86,true),(5,true),(1,false),(14,false)]
theorem der_30201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30201 :=
  CNF.rup_sound cl_30201 [cl_24067,cl_24065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24067 v h) (hints_cons _ _ _ (der_24065 v h) (by intro d hd; cases hd)))
def cl_30202 : CNF.NClause := [(86,true),(14,false),(22,false),(5,true),(1,false)]
theorem der_30202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30202 :=
  CNF.rup_sound cl_30202 [cl_24071,cl_24069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24071 v h) (hints_cons _ _ _ (der_24069 v h) (by intro d hd; cases hd)))
def cl_30203 : CNF.NClause := [(86,true),(14,false),(5,true),(1,false),(18,false)]
theorem der_30203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30203 :=
  CNF.rup_sound cl_30203 [cl_24073,cl_30202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24073 v h) (hints_cons _ _ _ (der_30202 v h) (by intro d hd; cases hd)))
def cl_30204 : CNF.NClause := [(29,true),(5,true),(18,false),(86,true),(1,false)]
theorem der_30204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30204 :=
  CNF.rup_sound cl_30204 [cl_24074,cl_30203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24074 v h) (hints_cons _ _ _ (der_30203 v h) (by intro d hd; cases hd)))
def cl_30205 : CNF.NClause := [(86,true),(14,false),(5,true),(18,true),(1,false)]
theorem der_30205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30205 :=
  CNF.rup_sound cl_30205 [cl_24075,cl_30202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24075 v h) (hints_cons _ _ _ (der_30202 v h) (by intro d hd; cases hd)))
def cl_30206 : CNF.NClause := [(24,false),(28,false),(13,false),(84,true),(2,false)]
theorem der_30206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30206 :=
  CNF.rup_sound cl_30206 [cl_24078,cl_24076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24078 v h) (hints_cons _ _ _ (der_24076 v h) (by intro d hd; cases hd)))
def cl_30208 : CNF.NClause := [(84,true),(16,false),(28,false),(5,true),(2,false)]
theorem der_30208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30208 :=
  CNF.rup_sound cl_30208 [cl_24081,cl_24077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24081 v h) (hints_cons _ _ _ (der_24077 v h) (by intro d hd; cases hd)))
def cl_30209 : CNF.NClause := [(28,false),(16,true),(13,false),(84,true),(2,false)]
theorem der_30209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30209 :=
  CNF.rup_sound cl_30209 [cl_24082,cl_30206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24082 v h) (hints_cons _ _ _ (der_30206 v h) (by intro d hd; cases hd)))
def cl_30210 : CNF.NClause := [(84,true),(5,true),(13,true),(28,false),(2,false)]
theorem der_30210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30210 :=
  CNF.rup_sound cl_30210 [cl_24083,cl_30208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24083 v h) (hints_cons _ _ _ (der_30208 v h) (by intro d hd; cases hd)))
def cl_30211 : CNF.NClause := [(84,true),(5,true),(24,false),(16,false),(2,false)]
theorem der_30211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30211 :=
  CNF.rup_sound cl_30211 [cl_24085,cl_24077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24085 v h) (hints_cons _ _ _ (der_24077 v h) (by intro d hd; cases hd)))
def cl_30212 : CNF.NClause := [(5,true),(24,false),(2,false),(13,false),(84,true)]
theorem der_30212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30212 :=
  CNF.rup_sound cl_30212 [cl_24086,cl_24084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24086 v h) (hints_cons _ _ _ (der_24084 v h) (by intro d hd; cases hd)))
def cl_30213 : CNF.NClause := [(84,true),(5,true),(13,true),(24,false),(2,false)]
theorem der_30213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30213 :=
  CNF.rup_sound cl_30213 [cl_24087,cl_30211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24087 v h) (hints_cons _ _ _ (der_30211 v h) (by intro d hd; cases hd)))
def cl_30215 : CNF.NClause := [(84,true),(16,false),(28,true),(5,true),(2,false)]
theorem der_30215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30215 :=
  CNF.rup_sound cl_30215 [cl_24089,cl_30211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24089 v h) (hints_cons _ _ _ (der_30211 v h) (by intro d hd; cases hd)))
def cl_30216 : CNF.NClause := [(84,true),(28,true),(13,false),(5,true),(2,false)]
theorem der_30216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30216 :=
  CNF.rup_sound cl_30216 [cl_24090,cl_30212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24090 v h) (hints_cons _ _ _ (der_30212 v h) (by intro d hd; cases hd)))
def cl_30217 : CNF.NClause := [(5,true),(27,false),(3,false),(85,true),(21,false)]
theorem der_30217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30217 :=
  CNF.rup_sound cl_30217 [cl_24093,cl_24092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24093 v h) (hints_cons _ _ _ (der_24092 v h) (by intro d hd; cases hd)))
def cl_30218 : CNF.NClause := [(3,false),(21,true),(19,false),(27,false),(85,true)]
theorem der_30218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30218 :=
  CNF.rup_sound cl_30218 [cl_24095,cl_24094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24095 v h) (hints_cons _ _ _ (der_24094 v h) (by intro d hd; cases hd)))
def cl_30219 : CNF.NClause := [(27,false),(21,true),(12,true),(3,false),(85,true)]
theorem der_30219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30219 :=
  CNF.rup_sound cl_30219 [cl_24097,cl_30218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24097 v h) (hints_cons _ _ _ (der_30218 v h) (by intro d hd; cases hd)))
def cl_30220 : CNF.NClause := [(85,true),(5,true),(12,true),(3,false),(21,false)]
theorem der_30220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30220 :=
  CNF.rup_sound cl_30220 [cl_24101,cl_30217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24101 v h) (hints_cons _ _ _ (der_30217 v h) (by intro d hd; cases hd)))
def cl_30221 : CNF.NClause := [(85,true),(19,false),(3,false),(12,false),(21,true)]
theorem der_30221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30221 :=
  CNF.rup_sound cl_30221 [cl_24102,cl_30218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24102 v h) (hints_cons _ _ _ (der_30218 v h) (by intro d hd; cases hd)))
def cl_30222 : CNF.NClause := [(3,false),(21,true),(12,true),(19,false),(85,true)]
theorem der_30222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30222 :=
  CNF.rup_sound cl_30222 [cl_24103,cl_30218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24103 v h) (hints_cons _ _ _ (der_30218 v h) (by intro d hd; cases hd)))
def cl_30223 : CNF.NClause := [(12,false),(21,true),(27,true),(3,false),(85,true)]
theorem der_30223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30223 :=
  CNF.rup_sound cl_30223 [cl_24104,cl_30221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24104 v h) (hints_cons _ _ _ (der_30221 v h) (by intro d hd; cases hd)))
def cl_30224 : CNF.NClause := [(28,false),(24,false),(13,false),(84,true),(16,false)]
theorem der_30224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30224 :=
  CNF.rup_sound cl_30224 [cl_24106,cl_24076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24106 v h) (hints_cons _ _ _ (der_24076 v h) (by intro d hd; cases hd)))
def cl_30225 : CNF.NClause := [(84,true),(5,true),(24,false),(28,false),(13,false)]
theorem der_30225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30225 :=
  CNF.rup_sound cl_30225 [cl_24107,cl_30224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24107 v h) (hints_cons _ _ _ (der_30224 v h) (by intro d hd; cases hd)))
def cl_30226 : CNF.NClause := [(28,false),(2,true),(13,false),(84,true),(16,false)]
theorem der_30226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30226 :=
  CNF.rup_sound cl_30226 [cl_24108,cl_30224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24108 v h) (hints_cons _ _ _ (der_30224 v h) (by intro d hd; cases hd)))
def cl_30227 : CNF.NClause := [(84,true),(24,true),(16,true),(28,false),(13,false)]
theorem der_30227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30227 :=
  CNF.rup_sound cl_30227 [cl_24109,cl_30209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24109 v h) (hints_cons _ _ _ (der_30209 v h) (by intro d hd; cases hd)))
def cl_30228 : CNF.NClause := [(24,false),(2,true),(13,false),(84,true),(16,false)]
theorem der_30228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30228 :=
  CNF.rup_sound cl_30228 [cl_24110,cl_30224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24110 v h) (hints_cons _ _ _ (der_30224 v h) (by intro d hd; cases hd)))
def cl_30229 : CNF.NClause := [(84,true),(28,true),(24,false),(13,false),(2,true)]
theorem der_30229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30229 :=
  CNF.rup_sound cl_30229 [cl_24111,cl_30228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24111 v h) (hints_cons _ _ _ (der_30228 v h) (by intro d hd; cases hd)))
def cl_30230 : CNF.NClause := [(84,true),(28,true),(2,true),(13,false),(16,false)]
theorem der_30230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30230 :=
  CNF.rup_sound cl_30230 [cl_24112,cl_30229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24112 v h) (hints_cons _ _ _ (der_30229 v h) (by intro d hd; cases hd)))
def cl_30231 : CNF.NClause := [(27,false),(85,true),(5,true),(12,false),(21,false)]
theorem der_30231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30231 :=
  CNF.rup_sound cl_30231 [cl_24114,cl_24113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24114 v h) (hints_cons _ _ _ (der_24113 v h) (by intro d hd; cases hd)))
def cl_30232 : CNF.NClause := [(27,false),(85,true),(19,false),(5,true),(12,false)]
theorem der_30232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30232 :=
  CNF.rup_sound cl_30232 [cl_24115,cl_30231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24115 v h) (hints_cons _ _ _ (der_30231 v h) (by intro d hd; cases hd)))
def cl_30233 : CNF.NClause := [(27,false),(85,true),(19,true),(5,true),(12,false)]
theorem der_30233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30233 :=
  CNF.rup_sound cl_30233 [cl_24116,cl_30231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24116 v h) (hints_cons _ _ _ (der_30231 v h) (by intro d hd; cases hd)))
def cl_30234 : CNF.NClause := [(85,true),(21,false),(19,false),(12,false),(5,true)]
theorem der_30234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30234 :=
  CNF.rup_sound cl_30234 [cl_24117,cl_30232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24117 v h) (hints_cons _ _ _ (der_30232 v h) (by intro d hd; cases hd)))
def cl_30235 : CNF.NClause := [(85,true),(12,false),(5,true),(21,false),(19,true)]
theorem der_30235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30235 :=
  CNF.rup_sound cl_30235 [cl_24118,cl_24100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24118 v h) (hints_cons _ _ _ (der_24100 v h) (by intro d hd; cases hd)))
def cl_30236 : CNF.NClause := [(19,false),(85,true),(3,true),(5,true),(12,false)]
theorem der_30236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30236 :=
  CNF.rup_sound cl_30236 [cl_24119,cl_30232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24119 v h) (hints_cons _ _ _ (der_30232 v h) (by intro d hd; cases hd)))
def cl_30237 : CNF.NClause := [(83,true),(26,false),(4,false),(5,true),(11,false)]
theorem der_30237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30237 :=
  CNF.rup_sound cl_30237 [cl_24123,cl_24121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24123 v h) (hints_cons _ _ _ (der_24121 v h) (by intro d hd; cases hd)))
def cl_30238 : CNF.NClause := [(17,false),(23,false),(4,false),(11,false),(83,true)]
theorem der_30238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30238 :=
  CNF.rup_sound cl_30238 [cl_24124,cl_24120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24124 v h) (hints_cons _ _ _ (der_24120 v h) (by intro d hd; cases hd)))
def cl_30240 : CNF.NClause := [(83,true),(5,true),(4,false),(17,false),(11,false)]
theorem der_30240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30240 :=
  CNF.rup_sound cl_30240 [cl_24126,cl_30238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24126 v h) (hints_cons _ _ _ (der_30238 v h) (by intro d hd; cases hd)))
def cl_30241 : CNF.NClause := [(17,true),(11,false),(5,true),(4,false),(83,true)]
theorem der_30241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30241 :=
  CNF.rup_sound cl_30241 [cl_24127,cl_30237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24127 v h) (hints_cons _ _ _ (der_30237 v h) (by intro d hd; cases hd)))
def cl_30242 : CNF.NClause := [(83,true),(26,false),(23,false),(5,true),(11,false)]
theorem der_30242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30242 :=
  CNF.rup_sound cl_30242 [cl_24130,cl_24128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24130 v h) (hints_cons _ _ _ (der_24128 v h) (by intro d hd; cases hd)))
def cl_30243 : CNF.NClause := [(83,true),(4,true),(26,false),(11,true),(23,false)]
theorem der_30243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30243 :=
  CNF.rup_sound cl_30243 [cl_24131,cl_24129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24131 v h) (hints_cons _ _ _ (der_24129 v h) (by intro d hd; cases hd)))
def cl_30244 : CNF.NClause := [(83,true),(26,false),(17,false),(5,true),(11,false)]
theorem der_30244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30244 :=
  CNF.rup_sound cl_30244 [cl_24132,cl_30242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24132 v h) (hints_cons _ _ _ (der_30242 v h) (by intro d hd; cases hd)))
def cl_30245 : CNF.NClause := [(4,true),(26,false),(11,true),(17,false),(83,true)]
theorem der_30245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30245 :=
  CNF.rup_sound cl_30245 [cl_24133,cl_24129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24133 v h) (hints_cons _ _ _ (der_24129 v h) (by intro d hd; cases hd)))
def cl_30246 : CNF.NClause := [(83,true),(23,true),(26,false),(5,true),(11,false)]
theorem der_30246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30246 :=
  CNF.rup_sound cl_30246 [cl_24134,cl_30237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24134 v h) (hints_cons _ _ _ (der_30237 v h) (by intro d hd; cases hd)))
def cl_30248 : CNF.NClause := [(17,true),(11,false),(5,true),(23,false),(83,true)]
theorem der_30248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30248 :=
  CNF.rup_sound cl_30248 [cl_24137,cl_30242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24137 v h) (hints_cons _ _ _ (der_30242 v h) (by intro d hd; cases hd)))
def cl_30249 : CNF.NClause := [(83,true),(11,false),(17,false),(26,true),(5,true)]
theorem der_30249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30249 :=
  CNF.rup_sound cl_30249 [cl_24138,cl_30240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24138 v h) (hints_cons _ _ _ (der_30240 v h) (by intro d hd; cases hd)))
def cl_30250 : CNF.NClause := [(18,true),(29,false),(14,true),(22,false),(86,true)]
theorem der_30250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30250 :=
  CNF.rup_sound cl_30250 [cl_24140,cl_29827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24140 v h) (hints_cons _ _ _ (der_29827 v h) (by intro d hd; cases hd)))
def cl_30251 : CNF.NClause := [(22,true),(29,false),(14,true),(18,false),(86,true)]
theorem der_30251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30251 :=
  CNF.rup_sound cl_30251 [cl_24141,cl_29825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24141 v h) (hints_cons _ _ _ (der_29825 v h) (by intro d hd; cases hd)))
def cl_30252 : CNF.NClause := [(86,true),(18,false),(22,false),(14,true),(5,true)]
theorem der_30252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30252 :=
  CNF.rup_sound cl_30252 [cl_24142,cl_29831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24142 v h) (hints_cons _ _ _ (der_29831 v h) (by intro d hd; cases hd)))
def cl_30253 : CNF.NClause := [(61,false),(62,false),(67,false),(72,false),(82,true)]
theorem der_30253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30253 :=
  CNF.rup_sound cl_30253 [cl_24144,cl_24143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24144 v h) (hints_cons _ _ _ (der_24143 v h) (by intro d hd; cases hd)))
def cl_30259 : CNF.NClause := [(80,true),(7,true),(15,false),(24,false),(3,false)]
theorem der_30259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30259 :=
  CNF.rup_sound cl_30259 [cl_24155,cl_24154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24155 v h) (hints_cons _ _ _ (der_24154 v h) (by intro d hd; cases hd)))
def cl_30260 : CNF.NClause := [(80,true),(7,true),(24,false),(3,false),(11,false)]
theorem der_30260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30260 :=
  CNF.rup_sound cl_30260 [cl_24156,cl_24154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24156 v h) (hints_cons _ _ _ (der_24154 v h) (by intro d hd; cases hd)))
def cl_30261 : CNF.NClause := [(80,true),(7,true),(15,true),(24,false),(3,false)]
theorem der_30261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30261 :=
  CNF.rup_sound cl_30261 [cl_24157,cl_30260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24157 v h) (hints_cons _ _ _ (der_30260 v h) (by intro d hd; cases hd)))
def cl_30262 : CNF.NClause := [(80,true),(7,true),(15,false),(3,false),(11,false)]
theorem der_30262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30262 :=
  CNF.rup_sound cl_30262 [cl_24158,cl_24154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24158 v h) (hints_cons _ _ _ (der_24154 v h) (by intro d hd; cases hd)))
def cl_30263 : CNF.NClause := [(80,true),(7,true),(11,true),(15,false),(3,false)]
theorem der_30263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30263 :=
  CNF.rup_sound cl_30263 [cl_24159,cl_30259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24159 v h) (hints_cons _ _ _ (der_30259 v h) (by intro d hd; cases hd)))
def cl_30264 : CNF.NClause := [(80,true),(7,true),(15,true),(3,false),(11,false)]
theorem der_30264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30264 :=
  CNF.rup_sound cl_30264 [cl_24160,cl_30260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24160 v h) (hints_cons _ _ _ (der_30260 v h) (by intro d hd; cases hd)))
def cl_30265 : CNF.NClause := [(20,false),(1,false),(71,true),(19,true),(13,false)]
theorem der_30265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30265 :=
  CNF.rup_sound cl_30265 [cl_24161,cl_30025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24161 v h) (hints_cons _ _ _ (der_30025 v h) (by intro d hd; cases hd)))
def cl_30266 : CNF.NClause := [(71,true),(20,false),(19,true),(7,true),(1,false)]
theorem der_30266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30266 :=
  CNF.rup_sound cl_30266 [cl_24162,cl_30265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24162 v h) (hints_cons _ _ _ (der_30265 v h) (by intro d hd; cases hd)))
def cl_30267 : CNF.NClause := [(20,true),(71,true),(7,true),(19,false),(13,false)]
theorem der_30267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30267 :=
  CNF.rup_sound cl_30267 [cl_24163,cl_30020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24163 v h) (hints_cons _ _ _ (der_30020 v h) (by intro d hd; cases hd)))
def cl_30268 : CNF.NClause := [(18,true),(28,true),(21,false),(73,true),(10,false)]
theorem der_30268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30268 :=
  CNF.rup_sound cl_30268 [cl_24166,cl_29995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24166 v h) (hints_cons _ _ _ (der_29995 v h) (by intro d hd; cases hd)))
def cl_30270 : CNF.NClause := [(68,true),(4,false),(29,false),(20,true),(8,false)]
theorem der_30270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30270 :=
  CNF.rup_sound cl_30270 [cl_24167,cl_29981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24167 v h) (hints_cons _ _ _ (der_29981 v h) (by intro d hd; cases hd)))
def cl_30271 : CNF.NClause := [(20,true),(70,true),(17,false),(6,true),(28,false)]
theorem der_30271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30271 :=
  CNF.rup_sound cl_30271 [cl_24169,cl_24060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24169 v h) (hints_cons _ _ _ (der_24060 v h) (by intro d hd; cases hd)))
def cl_30272 : CNF.NClause := [(70,true),(20,true),(14,false),(6,true),(17,false)]
theorem der_30272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30272 :=
  CNF.rup_sound cl_30272 [cl_24170,cl_30178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24170 v h) (hints_cons _ _ _ (der_30178 v h) (by intro d hd; cases hd)))
def cl_30273 : CNF.NClause := [(14,false),(70,true),(17,false),(3,false),(28,false)]
theorem der_30273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30273 :=
  CNF.rup_sound cl_30273 [cl_24171,cl_24021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24171 v h) (hints_cons _ _ _ (der_24021 v h) (by intro d hd; cases hd)))
def cl_30274 : CNF.NClause := [(69,true),(11,false),(2,true),(20,true),(9,false)]
theorem der_30274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30274 :=
  CNF.rup_sound cl_30274 [cl_24174,cl_29999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24174 v h) (hints_cons _ _ _ (der_29999 v h) (by intro d hd; cases hd)))
def cl_30276 : CNF.NClause := [(69,true),(20,true),(11,false),(9,false),(2,false)]
theorem der_30276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30276 :=
  CNF.rup_sound cl_30276 [cl_24176,cl_30000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24176 v h) (hints_cons _ _ _ (der_30000 v h) (by intro d hd; cases hd)))
def cl_30277 : CNF.NClause := [(1,false),(13,false),(71,true),(26,false),(19,false)]
theorem der_30277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30277 :=
  CNF.rup_sound cl_30277 [cl_24177,cl_23598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24177 v h) (hints_cons _ _ _ (der_23598 v h) (by intro d hd; cases hd)))
def cl_30278 : CNF.NClause := [(71,true),(19,false),(1,false),(13,false),(7,false)]
theorem der_30278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30278 :=
  CNF.rup_sound cl_30278 [cl_24178,cl_30277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24178 v h) (hints_cons _ _ _ (der_30277 v h) (by intro d hd; cases hd)))
def cl_30279 : CNF.NClause := [(68,true),(20,true),(4,false),(29,false),(12,true)]
theorem der_30279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30279 :=
  CNF.rup_sound cl_30279 [cl_24179,cl_30142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24179 v h) (hints_cons _ _ _ (der_30142 v h) (by intro d hd; cases hd)))
def cl_30280 : CNF.NClause := [(68,true),(29,false),(4,true),(8,true),(16,false)]
theorem der_30280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30280 :=
  CNF.rup_sound cl_30280 [cl_24181,cl_30159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24181 v h) (hints_cons _ _ _ (der_30159 v h) (by intro d hd; cases hd)))
def cl_30281 : CNF.NClause := [(69,true),(2,true),(20,true),(27,false),(11,false)]
theorem der_30281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30281 :=
  CNF.rup_sound cl_30281 [cl_24182,cl_24173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24182 v h) (hints_cons _ _ _ (der_24173 v h) (by intro d hd; cases hd)))
def cl_30282 : CNF.NClause := [(26,false),(1,false),(13,false),(71,true),(7,false)]
theorem der_30282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30282 :=
  CNF.rup_sound cl_30282 [cl_24183,cl_30277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24183 v h) (hints_cons _ _ _ (der_30277 v h) (by intro d hd; cases hd)))
def cl_30283 : CNF.NClause := [(7,false),(1,false),(71,true),(20,true),(13,false)]
theorem der_30283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30283 :=
  CNF.rup_sound cl_30283 [cl_24184,cl_30278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24184 v h) (hints_cons _ _ _ (der_30278 v h) (by intro d hd; cases hd)))
def cl_30284 : CNF.NClause := [(69,true),(20,true),(2,true),(11,false),(18,false)]
theorem der_30284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30284 :=
  CNF.rup_sound cl_30284 [cl_24186,cl_30281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24186 v h) (hints_cons _ _ _ (der_30281 v h) (by intro d hd; cases hd)))
def cl_30285 : CNF.NClause := [(6,false),(14,true),(3,false),(70,true),(17,false)]
theorem der_30285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30285 :=
  CNF.rup_sound cl_30285 [cl_24187,cl_30014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24187 v h) (hints_cons _ _ _ (der_30014 v h) (by intro d hd; cases hd)))
def cl_30286 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(26,false)]
theorem der_30286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30286 :=
  CNF.rup_sound cl_30286 [cl_24188,cl_23598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24188 v h) (hints_cons _ _ _ (der_23598 v h) (by intro d hd; cases hd)))
def cl_30287 : CNF.NClause := [(29,false),(86,true),(5,true),(22,false),(18,false)]
theorem der_30287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30287 :=
  CNF.rup_sound cl_30287 [cl_24189,cl_29831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24189 v h) (hints_cons _ _ _ (der_29831 v h) (by intro d hd; cases hd)))
def cl_30289 : CNF.NClause := [(27,false),(24,false),(76,true),(17,false),(1,true)]
theorem der_30289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30289 :=
  CNF.rup_sound cl_30289 [cl_24193,cl_24191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24193 v h) (hints_cons _ _ _ (der_24191 v h) (by intro d hd; cases hd)))
def cl_30290 : CNF.NClause := [(76,true),(1,true),(24,false),(27,false),(8,false)]
theorem der_30290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30290 :=
  CNF.rup_sound cl_30290 [cl_24195,cl_30289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24195 v h) (hints_cons _ _ _ (der_30289 v h) (by intro d hd; cases hd)))
def cl_30291 : CNF.NClause := [(27,false),(76,true),(8,false),(17,false),(1,true)]
theorem der_30291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30291 :=
  CNF.rup_sound cl_30291 [cl_24197,cl_24196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24197 v h) (hints_cons _ _ _ (der_24196 v h) (by intro d hd; cases hd)))
def cl_30293 : CNF.NClause := [(76,true),(27,false),(17,true),(8,false),(1,true)]
theorem der_30293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30293 :=
  CNF.rup_sound cl_30293 [cl_24199,cl_30290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24199 v h) (hints_cons _ _ _ (der_30290 v h) (by intro d hd; cases hd)))
def cl_30295 : CNF.NClause := [(76,true),(17,false),(8,false),(24,false),(1,true)]
theorem der_30295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30295 :=
  CNF.rup_sound cl_30295 [cl_24201,cl_30290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24201 v h) (hints_cons _ _ _ (der_30290 v h) (by intro d hd; cases hd)))
def cl_30296 : CNF.NClause := [(76,true),(24,false),(1,true),(10,false),(8,false)]
theorem der_30296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30296 :=
  CNF.rup_sound cl_30296 [cl_24202,cl_30295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24202 v h) (hints_cons _ _ _ (der_30295 v h) (by intro d hd; cases hd)))
def cl_30297 : CNF.NClause := [(76,true),(10,true),(1,true),(24,false),(8,false)]
theorem der_30297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30297 :=
  CNF.rup_sound cl_30297 [cl_24203,cl_30295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24203 v h) (hints_cons _ _ _ (der_30295 v h) (by intro d hd; cases hd)))
def cl_30299 : CNF.NClause := [(76,true),(27,true),(17,false),(8,false),(1,true)]
theorem der_30299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30299 :=
  CNF.rup_sound cl_30299 [cl_24205,cl_30295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24205 v h) (hints_cons _ _ _ (der_30295 v h) (by intro d hd; cases hd)))
def cl_30300 : CNF.NClause := [(76,true),(17,true),(1,true),(10,false),(8,false)]
theorem der_30300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30300 :=
  CNF.rup_sound cl_30300 [cl_24206,cl_30296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24206 v h) (hints_cons _ _ _ (der_30296 v h) (by intro d hd; cases hd)))
def cl_30301 : CNF.NClause := [(19,false),(71,true),(26,false),(20,false),(13,false)]
theorem der_30301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30301 :=
  CNF.rup_sound cl_30301 [cl_24207,cl_23621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24207 v h) (hints_cons _ _ _ (der_23621 v h) (by intro d hd; cases hd)))
def cl_30302 : CNF.NClause := [(7,false),(71,true),(26,false),(20,false),(19,false)]
theorem der_30302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30302 :=
  CNF.rup_sound cl_30302 [cl_24208,cl_30301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24208 v h) (hints_cons _ _ _ (der_30301 v h) (by intro d hd; cases hd)))
def cl_30303 : CNF.NClause := [(7,false),(20,false),(71,true),(26,false),(13,false)]
theorem der_30303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30303 :=
  CNF.rup_sound cl_30303 [cl_24209,cl_30301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24209 v h) (hints_cons _ _ _ (der_30301 v h) (by intro d hd; cases hd)))
def cl_30304 : CNF.NClause := [(7,false),(19,true),(71,true),(26,false),(20,false)]
theorem der_30304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30304 :=
  CNF.rup_sound cl_30304 [cl_24210,cl_30303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24210 v h) (hints_cons _ _ _ (der_30303 v h) (by intro d hd; cases hd)))
def cl_30306 : CNF.NClause := [(26,false),(1,true),(71,true),(19,false),(7,false)]
theorem der_30306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30306 :=
  CNF.rup_sound cl_30306 [cl_24212,cl_30302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24212 v h) (hints_cons _ _ _ (der_30302 v h) (by intro d hd; cases hd)))
def cl_30307 : CNF.NClause := [(7,false),(26,false),(19,true),(71,true),(13,false)]
theorem der_30307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30307 :=
  CNF.rup_sound cl_30307 [cl_24213,cl_30282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24213 v h) (hints_cons _ _ _ (der_30282 v h) (by intro d hd; cases hd)))
def cl_30309 : CNF.NClause := [(7,false),(19,false),(71,true),(20,false),(1,true)]
theorem der_30309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30309 :=
  CNF.rup_sound cl_30309 [cl_24216,cl_30306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24216 v h) (hints_cons _ _ _ (der_30306 v h) (by intro d hd; cases hd)))
def cl_30310 : CNF.NClause := [(7,false),(20,false),(71,true),(1,true),(13,false)]
theorem der_30310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30310 :=
  CNF.rup_sound cl_30310 [cl_24217,cl_30309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24217 v h) (hints_cons _ _ _ (der_30309 v h) (by intro d hd; cases hd)))
def cl_30311 : CNF.NClause := [(7,false),(20,false),(26,true),(71,true),(1,true)]
theorem der_30311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30311 :=
  CNF.rup_sound cl_30311 [cl_24218,cl_30309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24218 v h) (hints_cons _ _ _ (der_30309 v h) (by intro d hd; cases hd)))
def cl_30313 : CNF.NClause := [(71,true),(20,true),(1,true),(19,false),(7,false)]
theorem der_30313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30313 :=
  CNF.rup_sound cl_30313 [cl_24220,cl_30306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24220 v h) (hints_cons _ _ _ (der_30306 v h) (by intro d hd; cases hd)))
def cl_30314 : CNF.NClause := [(71,true),(26,true),(1,true),(13,false),(7,false)]
theorem der_30314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30314 :=
  CNF.rup_sound cl_30314 [cl_24221,cl_30310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24221 v h) (hints_cons _ _ _ (der_30310 v h) (by intro d hd; cases hd)))
def cl_30315 : CNF.NClause := [(29,false),(5,false),(18,false),(14,true),(86,true)]
theorem der_30315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30315 :=
  CNF.rup_sound cl_30315 [cl_24223,cl_30251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24223 v h) (hints_cons _ _ _ (der_30251 v h) (by intro d hd; cases hd)))
def cl_30316 : CNF.NClause := [(29,false),(86,true),(18,false),(5,false),(1,true)]
theorem der_30316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30316 :=
  CNF.rup_sound cl_30316 [cl_24226,cl_30315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24226 v h) (hints_cons _ _ _ (der_30315 v h) (by intro d hd; cases hd)))
def cl_30317 : CNF.NClause := [(29,false),(22,true),(1,true),(86,true),(5,false)]
theorem der_30317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30317 :=
  CNF.rup_sound cl_30317 [cl_24228,cl_29825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24228 v h) (hints_cons _ _ _ (der_29825 v h) (by intro d hd; cases hd)))
def cl_30318 : CNF.NClause := [(22,true),(29,false),(14,true),(5,false),(86,true)]
theorem der_30318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30318 :=
  CNF.rup_sound cl_30318 [cl_24229,cl_30251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24229 v h) (hints_cons _ _ _ (der_30251 v h) (by intro d hd; cases hd)))
def cl_30319 : CNF.NClause := [(5,false),(86,true),(22,false),(1,true),(18,false)]
theorem der_30319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30319 :=
  CNF.rup_sound cl_30319 [cl_24231,cl_30316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24231 v h) (hints_cons _ _ _ (der_30316 v h) (by intro d hd; cases hd)))
def cl_30321 : CNF.NClause := [(18,true),(86,true),(14,true),(22,false),(5,false)]
theorem der_30321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30321 :=
  CNF.rup_sound cl_30321 [cl_24233,cl_29827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24233 v h) (hints_cons _ _ _ (der_29827 v h) (by intro d hd; cases hd)))
def cl_30322 : CNF.NClause := [(14,false),(86,true),(1,true),(5,false),(18,false)]
theorem der_30322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30322 :=
  CNF.rup_sound cl_30322 [cl_24234,cl_30316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24234 v h) (hints_cons _ _ _ (der_30316 v h) (by intro d hd; cases hd)))
def cl_30323 : CNF.NClause := [(5,false),(18,false),(86,true),(14,true),(1,true)]
theorem der_30323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30323 :=
  CNF.rup_sound cl_30323 [cl_24235,cl_30315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24235 v h) (hints_cons _ _ _ (der_30315 v h) (by intro d hd; cases hd)))
def cl_30324 : CNF.NClause := [(14,false),(5,false),(29,true),(86,true),(1,true)]
theorem der_30324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30324 :=
  CNF.rup_sound cl_30324 [cl_24236,cl_30322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24236 v h) (hints_cons _ _ _ (der_30322 v h) (by intro d hd; cases hd)))
def cl_30325 : CNF.NClause := [(9,true),(28,false),(1,true),(23,false),(81,true)]
theorem der_30325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30325 :=
  CNF.rup_sound cl_30325 [cl_24240,cl_24238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24240 v h) (hints_cons _ _ _ (der_24238 v h) (by intro d hd; cases hd)))
def cl_30326 : CNF.NClause := [(81,true),(1,true),(9,true),(15,false),(28,false)]
theorem der_30326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30326 :=
  CNF.rup_sound cl_30326 [cl_24242,cl_24238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24242 v h) (hints_cons _ _ _ (der_24238 v h) (by intro d hd; cases hd)))
def cl_30327 : CNF.NClause := [(81,true),(15,true),(9,true),(28,false),(12,false)]
theorem der_30327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30327 :=
  CNF.rup_sound cl_30327 [cl_24243,cl_24239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24243 v h) (hints_cons _ _ _ (der_24239 v h) (by intro d hd; cases hd)))
def cl_30328 : CNF.NClause := [(28,true),(81,true),(15,false),(23,false),(12,false)]
theorem der_30328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30328 :=
  CNF.rup_sound cl_30328 [cl_24244,cl_23553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24244 v h) (hints_cons _ _ _ (der_23553 v h) (by intro d hd; cases hd)))
def cl_30329 : CNF.NClause := [(28,true),(81,true),(9,true),(15,false),(23,false)]
theorem der_30329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30329 :=
  CNF.rup_sound cl_30329 [cl_24245,cl_30328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24245 v h) (hints_cons _ _ _ (der_30328 v h) (by intro d hd; cases hd)))
def cl_30330 : CNF.NClause := [(24,false),(17,false),(27,true),(1,true),(76,true)]
theorem der_30330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30330 :=
  CNF.rup_sound cl_30330 [cl_24248,cl_30295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24248 v h) (hints_cons _ _ _ (der_30295 v h) (by intro d hd; cases hd)))
def cl_30331 : CNF.NClause := [(86,true),(29,false),(5,true),(14,false),(18,false)]
theorem der_30331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30331 :=
  CNF.rup_sound cl_30331 [cl_24249,cl_24065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24249 v h) (hints_cons _ _ _ (der_24065 v h) (by intro d hd; cases hd)))
def cl_30332 : CNF.NClause := [(7,true),(20,false),(71,true),(26,false),(13,false)]
theorem der_30332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30332 :=
  CNF.rup_sound cl_30332 [cl_24250,cl_23621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24250 v h) (hints_cons _ _ _ (der_23621 v h) (by intro d hd; cases hd)))
def cl_30333 : CNF.NClause := [(26,true),(13,false),(20,false),(71,true),(1,true)]
theorem der_30333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30333 :=
  CNF.rup_sound cl_30333 [cl_24251,cl_30314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24251 v h) (hints_cons _ _ _ (der_30314 v h) (by intro d hd; cases hd)))
def cl_30334 : CNF.NClause := [(81,true),(28,false),(15,false),(23,false),(1,true)]
theorem der_30334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30334 :=
  CNF.rup_sound cl_30334 [cl_24252,cl_30326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24252 v h) (hints_cons _ _ _ (der_30326 v h) (by intro d hd; cases hd)))
def cl_30336 : CNF.NClause := [(81,true),(1,true),(15,false),(28,false),(12,false)]
theorem der_30336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30336 :=
  CNF.rup_sound cl_30336 [cl_24255,cl_24241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24255 v h) (hints_cons _ _ _ (der_24241 v h) (by intro d hd; cases hd)))
def cl_30337 : CNF.NClause := [(81,true),(15,false),(9,false),(12,false),(1,true)]
theorem der_30337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30337 :=
  CNF.rup_sound cl_30337 [cl_24256,cl_30336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24256 v h) (hints_cons _ _ _ (der_30336 v h) (by intro d hd; cases hd)))
def cl_30338 : CNF.NClause := [(69,true),(27,true),(2,true),(11,false),(9,false)]
theorem der_30338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30338 :=
  CNF.rup_sound cl_30338 [cl_24257,cl_30274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24257 v h) (hints_cons _ _ _ (der_30274 v h) (by intro d hd; cases hd)))
def cl_30339 : CNF.NClause := [(69,true),(27,true),(20,false),(11,false),(9,false)]
theorem der_30339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30339 :=
  CNF.rup_sound cl_30339 [cl_24258,cl_23584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24258 v h) (hints_cons _ _ _ (der_23584 v h) (by intro d hd; cases hd)))
def cl_30341 : CNF.NClause := [(83,true),(5,true),(26,true),(4,false),(17,false)]
theorem der_30341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30341 :=
  CNF.rup_sound cl_30341 [cl_24262,cl_30240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24262 v h) (hints_cons _ _ _ (der_30240 v h) (by intro d hd; cases hd)))
def cl_30343 : CNF.NClause := [(26,true),(83,true),(4,false),(17,false),(11,false)]
theorem der_30343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30343 :=
  CNF.rup_sound cl_30343 [cl_24264,cl_30240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24264 v h) (hints_cons _ _ _ (der_30240 v h) (by intro d hd; cases hd)))
def cl_30344 : CNF.NClause := [(74,true),(10,false),(19,false),(29,false),(2,false)]
theorem der_30344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30344 :=
  CNF.rup_sound cl_30344 [cl_24265,cl_30164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24265 v h) (hints_cons _ _ _ (der_30164 v h) (by intro d hd; cases hd)))
def cl_30345 : CNF.NClause := [(12,false),(28,false),(9,false),(81,true),(15,false)]
theorem der_30345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30345 :=
  CNF.rup_sound cl_30345 [cl_24269,cl_30337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24269 v h) (hints_cons _ _ _ (der_30337 v h) (by intro d hd; cases hd)))
def cl_30346 : CNF.NClause := [(12,false),(28,true),(1,false),(81,true),(15,false)]
theorem der_30346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30346 :=
  CNF.rup_sound cl_30346 [cl_24270,cl_24268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24270 v h) (hints_cons _ _ _ (der_24268 v h) (by intro d hd; cases hd)))
def cl_30347 : CNF.NClause := [(68,true),(8,false),(4,false),(29,false),(20,false)]
theorem der_30347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30347 :=
  CNF.rup_sound cl_30347 [cl_24272,cl_29981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24272 v h) (hints_cons _ _ _ (der_29981 v h) (by intro d hd; cases hd)))
def cl_30348 : CNF.NClause := [(78,true),(15,false),(4,false),(13,false),(6,false)]
theorem der_30348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30348 :=
  CNF.rup_sound cl_30348 [cl_24274,cl_30181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24274 v h) (hints_cons _ _ _ (der_30181 v h) (by intro d hd; cases hd)))
def cl_30349 : CNF.NClause := [(75,true),(26,true),(3,false),(10,false),(9,false)]
theorem der_30349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30349 :=
  CNF.rup_sound cl_30349 [cl_24276,cl_24273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24276 v h) (hints_cons _ _ _ (der_24273 v h) (by intro d hd; cases hd)))
def cl_30350 : CNF.NClause := [(81,true),(28,false),(23,false),(9,false),(15,false)]
theorem der_30350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30350 :=
  CNF.rup_sound cl_30350 [cl_24277,cl_30334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24277 v h) (hints_cons _ _ _ (der_30334 v h) (by intro d hd; cases hd)))
def cl_30351 : CNF.NClause := [(81,true),(15,false),(28,false),(12,true),(9,false)]
theorem der_30351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30351 :=
  CNF.rup_sound cl_30351 [cl_24279,cl_30350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24279 v h) (hints_cons _ _ _ (der_30350 v h) (by intro d hd; cases hd)))
def cl_30352 : CNF.NClause := [(81,true),(28,false),(1,false),(12,true),(9,false)]
theorem der_30352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30352 :=
  CNF.rup_sound cl_30352 [cl_24280,cl_30351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24280 v h) (hints_cons _ _ _ (der_30351 v h) (by intro d hd; cases hd)))
def cl_30353 : CNF.NClause := [(1,false),(15,false),(23,false),(9,false),(81,true)]
theorem der_30353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30353 :=
  CNF.rup_sound cl_30353 [cl_24281,cl_30350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24281 v h) (hints_cons _ _ _ (der_30350 v h) (by intro d hd; cases hd)))
def cl_30354 : CNF.NClause := [(81,true),(23,false),(1,false),(9,false),(12,true)]
theorem der_30354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30354 :=
  CNF.rup_sound cl_30354 [cl_24282,cl_24278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24282 v h) (hints_cons _ _ _ (der_24278 v h) (by intro d hd; cases hd)))
def cl_30355 : CNF.NClause := [(81,true),(15,false),(1,false),(9,false),(12,true)]
theorem der_30355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30355 :=
  CNF.rup_sound cl_30355 [cl_24283,cl_30352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24283 v h) (hints_cons _ _ _ (der_30352 v h) (by intro d hd; cases hd)))
def cl_30356 : CNF.NClause := [(81,true),(23,true),(1,false),(9,false),(12,true)]
theorem der_30356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30356 :=
  CNF.rup_sound cl_30356 [cl_24284,cl_30352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24284 v h) (hints_cons _ _ _ (der_30352 v h) (by intro d hd; cases hd)))
def cl_30358 : CNF.NClause := [(27,false),(19,false),(3,true),(5,true),(85,true)]
theorem der_30358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30358 :=
  CNF.rup_sound cl_30358 [cl_24286,cl_30236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24286 v h) (hints_cons _ _ _ (der_30236 v h) (by intro d hd; cases hd)))
def cl_30359 : CNF.NClause := [(3,true),(21,false),(5,true),(19,false),(85,true)]
theorem der_30359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30359 :=
  CNF.rup_sound cl_30359 [cl_24287,cl_30236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24287 v h) (hints_cons _ _ _ (der_30236 v h) (by intro d hd; cases hd)))
def cl_30360 : CNF.NClause := [(64,false),(17,true),(2,true),(12,true),(7,true)]
theorem der_30360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30360 :=
  CNF.rup_sound cl_30360 [cl_15062,cl_23353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15062 v h) (hints_cons _ _ _ (der_23353 v h) (by intro d hd; cases hd)))
def cl_30361 : CNF.NClause := [(3,false),(19,true),(12,true),(5,false),(85,true)]
theorem der_30361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30361 :=
  CNF.rup_sound cl_30361 [cl_24289,cl_24288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24289 v h) (hints_cons _ _ _ (der_24288 v h) (by intro d hd; cases hd)))
def cl_30362 : CNF.NClause := [(84,true),(5,true),(24,false),(16,true),(28,false)]
theorem der_30362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30362 :=
  CNF.rup_sound cl_30362 [cl_24290,cl_30225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24290 v h) (hints_cons _ _ _ (der_30225 v h) (by intro d hd; cases hd)))
def cl_30363 : CNF.NClause := [(69,true),(2,true),(27,false),(11,false),(9,false)]
theorem der_30363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30363 :=
  CNF.rup_sound cl_30363 [cl_24291,cl_24173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24291 v h) (hints_cons _ _ _ (der_24173 v h) (by intro d hd; cases hd)))
def cl_30364 : CNF.NClause := [(79,true),(14,false),(2,true),(15,true),(26,false)]
theorem der_30364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30364 :=
  CNF.rup_sound cl_30364 [cl_24292,cl_23638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24292 v h) (hints_cons _ _ _ (der_23638 v h) (by intro d hd; cases hd)))
def cl_30365 : CNF.NClause := [(79,true),(2,true),(26,false),(15,false),(21,false)]
theorem der_30365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30365 :=
  CNF.rup_sound cl_30365 [cl_24293,cl_29816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24293 v h) (hints_cons _ _ _ (der_29816 v h) (by intro d hd; cases hd)))
def cl_30366 : CNF.NClause := [(68,true),(16,true),(12,true),(20,false),(4,false)]
theorem der_30366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30366 :=
  CNF.rup_sound cl_30366 [cl_24295,cl_30141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24295 v h) (hints_cons _ _ _ (der_30141 v h) (by intro d hd; cases hd)))
def cl_30367 : CNF.NClause := [(68,true),(20,false),(4,false),(8,false),(16,false)]
theorem der_30367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30367 :=
  CNF.rup_sound cl_30367 [cl_24296,cl_30347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24296 v h) (hints_cons _ _ _ (der_30347 v h) (by intro d hd; cases hd)))
def cl_30368 : CNF.NClause := [(86,true),(14,false),(5,true),(22,false),(18,false)]
theorem der_30368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30368 :=
  CNF.rup_sound cl_30368 [cl_24297,cl_30202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24297 v h) (hints_cons _ _ _ (der_30202 v h) (by intro d hd; cases hd)))
def cl_30369 : CNF.NClause := [(86,true),(14,false),(29,true),(22,false),(18,false)]
theorem der_30369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30369 :=
  CNF.rup_sound cl_30369 [cl_24298,cl_30368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24298 v h) (hints_cons _ _ _ (der_30368 v h) (by intro d hd; cases hd)))
def cl_30370 : CNF.NClause := [(74,true),(29,true),(10,false),(19,false),(6,false)]
theorem der_30370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30370 :=
  CNF.rup_sound cl_30370 [cl_24299,cl_24266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24299 v h) (hints_cons _ _ _ (der_24266 v h) (by intro d hd; cases hd)))
def cl_30371 : CNF.NClause := [(80,true),(3,false),(15,false),(24,false),(11,false)]
theorem der_30371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30371 :=
  CNF.rup_sound cl_30371 [cl_24300,cl_24154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24300 v h) (hints_cons _ _ _ (der_24154 v h) (by intro d hd; cases hd)))
def cl_30372 : CNF.NClause := [(29,true),(68,true),(12,true),(4,false),(20,false)]
theorem der_30372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30372 :=
  CNF.rup_sound cl_30372 [cl_24301,cl_30366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24301 v h) (hints_cons _ _ _ (der_30366 v h) (by intro d hd; cases hd)))
def cl_30373 : CNF.NClause := [(14,true),(1,false),(5,false),(86,true),(22,false)]
theorem der_30373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30373 :=
  CNF.rup_sound cl_30373 [cl_24303,cl_30011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24303 v h) (hints_cons _ _ _ (der_30011 v h) (by intro d hd; cases hd)))
def cl_30374 : CNF.NClause := [(22,true),(1,false),(86,true),(14,true),(5,false)]
theorem der_30374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30374 :=
  CNF.rup_sound cl_30374 [cl_24304,cl_29825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24304 v h) (hints_cons _ _ _ (der_29825 v h) (by intro d hd; cases hd)))
def cl_30375 : CNF.NClause := [(80,true),(3,false),(15,false),(11,false),(29,false)]
theorem der_30375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30375 :=
  CNF.rup_sound cl_30375 [cl_24305,cl_24150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24305 v h) (hints_cons _ _ _ (der_24150 v h) (by intro d hd; cases hd)))
def cl_30376 : CNF.NClause := [(80,true),(15,false),(3,false),(11,false),(7,false)]
theorem der_30376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30376 :=
  CNF.rup_sound cl_30376 [cl_24306,cl_30375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24306 v h) (hints_cons _ _ _ (der_30375 v h) (by intro d hd; cases hd)))
def cl_30377 : CNF.NClause := [(24,true),(28,false),(5,false),(13,false),(84,true)]
theorem der_30377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30377 :=
  CNF.rup_sound cl_30377 [cl_24307,cl_30227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24307 v h) (hints_cons _ _ _ (der_30227 v h) (by intro d hd; cases hd)))
def cl_30378 : CNF.NClause := [(84,true),(24,true),(5,false),(13,false),(16,false)]
theorem der_30378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30378 :=
  CNF.rup_sound cl_30378 [cl_24308,cl_30377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24308 v h) (hints_cons _ _ _ (der_30377 v h) (by intro d hd; cases hd)))
def cl_30379 : CNF.NClause := [(76,true),(27,false),(1,true),(10,true),(17,false)]
theorem der_30379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30379 :=
  CNF.rup_sound cl_30379 [cl_24309,cl_30291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24309 v h) (hints_cons _ _ _ (der_30291 v h) (by intro d hd; cases hd)))
def cl_30380 : CNF.NClause := [(76,true),(10,false),(17,false),(27,false),(8,false)]
theorem der_30380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30380 :=
  CNF.rup_sound cl_30380 [cl_24310,cl_24196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24310 v h) (hints_cons _ _ _ (der_24196 v h) (by intro d hd; cases hd)))
def cl_30381 : CNF.NClause := [(27,true),(10,false),(76,true),(17,false),(1,false)]
theorem der_30381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30381 :=
  CNF.rup_sound cl_30381 [cl_24311,cl_30156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24311 v h) (hints_cons _ _ _ (der_30156 v h) (by intro d hd; cases hd)))
def cl_30382 : CNF.NClause := [(80,true),(11,false),(7,true),(24,true),(15,false)]
theorem der_30382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30382 :=
  CNF.rup_sound cl_30382 [cl_24313,cl_30262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24313 v h) (hints_cons _ _ _ (der_30262 v h) (by intro d hd; cases hd)))
def cl_30384 : CNF.NClause := [(76,true),(10,false),(1,true),(17,false),(27,false)]
theorem der_30384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30384 :=
  CNF.rup_sound cl_30384 [cl_24315,cl_30380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24315 v h) (hints_cons _ _ _ (der_30380 v h) (by intro d hd; cases hd)))
def cl_30385 : CNF.NClause := [(76,true),(10,false),(8,true),(27,true),(17,false)]
theorem der_30385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30385 :=
  CNF.rup_sound cl_30385 [cl_24316,cl_30155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24316 v h) (hints_cons _ _ _ (der_30155 v h) (by intro d hd; cases hd)))
def cl_30386 : CNF.NClause := [(80,true),(3,false),(11,false),(29,false),(24,false)]
theorem der_30386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30386 :=
  CNF.rup_sound cl_30386 [cl_24317,cl_24148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24317 v h) (hints_cons _ _ _ (der_24148 v h) (by intro d hd; cases hd)))
def cl_30387 : CNF.NClause := [(80,true),(15,true),(3,false),(11,false),(29,false)]
theorem der_30387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30387 :=
  CNF.rup_sound cl_30387 [cl_24318,cl_30386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24318 v h) (hints_cons _ _ _ (der_30386 v h) (by intro d hd; cases hd)))
def cl_30388 : CNF.NClause := [(29,true),(11,false),(24,false),(80,true),(3,false)]
theorem der_30388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30388 :=
  CNF.rup_sound cl_30388 [cl_24319,cl_30371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24319 v h) (hints_cons _ _ _ (der_30371 v h) (by intro d hd; cases hd)))
def cl_30389 : CNF.NClause := [(80,true),(29,true),(15,true),(3,false),(11,false)]
theorem der_30389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30389 :=
  CNF.rup_sound cl_30389 [cl_24320,cl_30388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24320 v h) (hints_cons _ _ _ (der_30388 v h) (by intro d hd; cases hd)))
def cl_30390 : CNF.NClause := [(81,true),(23,false),(28,false),(1,true),(12,false)]
theorem der_30390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30390 :=
  CNF.rup_sound cl_30390 [cl_24321,cl_30325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24321 v h) (hints_cons _ _ _ (der_30325 v h) (by intro d hd; cases hd)))
def cl_30391 : CNF.NClause := [(81,true),(15,true),(1,true),(28,false),(12,false)]
theorem der_30391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30391 :=
  CNF.rup_sound cl_30391 [cl_24322,cl_30327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24322 v h) (hints_cons _ _ _ (der_30327 v h) (by intro d hd; cases hd)))
def cl_30392 : CNF.NClause := [(81,true),(1,true),(9,false),(23,false),(12,false)]
theorem der_30392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30392 :=
  CNF.rup_sound cl_30392 [cl_24323,cl_30390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24323 v h) (hints_cons _ _ _ (der_30390 v h) (by intro d hd; cases hd)))
def cl_30393 : CNF.NClause := [(81,true),(28,true),(9,false),(1,true),(12,false)]
theorem der_30393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30393 :=
  CNF.rup_sound cl_30393 [cl_24324,cl_30392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24324 v h) (hints_cons _ _ _ (der_30392 v h) (by intro d hd; cases hd)))
def cl_30394 : CNF.NClause := [(81,true),(15,true),(28,false),(23,false),(12,false)]
theorem der_30394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30394 :=
  CNF.rup_sound cl_30394 [cl_24325,cl_30391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24325 v h) (hints_cons _ _ _ (der_30391 v h) (by intro d hd; cases hd)))
def cl_30395 : CNF.NClause := [(28,false),(15,true),(1,false),(81,true),(12,false)]
theorem der_30395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30395 :=
  CNF.rup_sound cl_30395 [cl_24326,cl_30394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24326 v h) (hints_cons _ _ _ (der_30394 v h) (by intro d hd; cases hd)))
def cl_30396 : CNF.NClause := [(28,true),(23,false),(9,false),(81,true),(12,false)]
theorem der_30396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30396 :=
  CNF.rup_sound cl_30396 [cl_24327,cl_30393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24327 v h) (hints_cons _ _ _ (der_30393 v h) (by intro d hd; cases hd)))
def cl_30397 : CNF.NClause := [(12,false),(28,true),(1,false),(9,false),(81,true)]
theorem der_30397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30397 :=
  CNF.rup_sound cl_30397 [cl_24328,cl_30346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24328 v h) (hints_cons _ _ _ (der_30346 v h) (by intro d hd; cases hd)))
def cl_30399 : CNF.NClause := [(78,true),(22,true),(4,false),(27,false),(13,false)]
theorem der_30399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30399 :=
  CNF.rup_sound cl_30399 [cl_24330,cl_30182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24330 v h) (hints_cons _ _ _ (der_30182 v h) (by intro d hd; cases hd)))
def cl_30400 : CNF.NClause := [(78,true),(15,true),(4,false),(13,false),(22,false)]
theorem der_30400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30400 :=
  CNF.rup_sound cl_30400 [cl_24331,cl_30183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24331 v h) (hints_cons _ _ _ (der_30183 v h) (by intro d hd; cases hd)))
def cl_30401 : CNF.NClause := [(78,true),(27,true),(22,true),(4,false),(13,false)]
theorem der_30401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30401 :=
  CNF.rup_sound cl_30401 [cl_24332,cl_30185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24332 v h) (hints_cons _ _ _ (der_30185 v h) (by intro d hd; cases hd)))
def cl_30402 : CNF.NClause := [(15,true),(79,true),(8,false),(26,false),(21,false)]
theorem der_30402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30402 :=
  CNF.rup_sound cl_30402 [cl_24333,cl_29828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24333 v h) (hints_cons _ _ _ (der_29828 v h) (by intro d hd; cases hd)))
def cl_30403 : CNF.NClause := [(21,true),(8,false),(2,false),(26,false),(79,true)]
theorem der_30403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30403 :=
  CNF.rup_sound cl_30403 [cl_24334,cl_30039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24334 v h) (hints_cons _ _ _ (der_30039 v h) (by intro d hd; cases hd)))
def cl_30405 : CNF.NClause := [(79,true),(14,false),(15,true),(26,true),(2,false)]
theorem der_30405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30405 :=
  CNF.rup_sound cl_30405 [cl_24336,cl_30140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24336 v h) (hints_cons _ _ _ (der_30140 v h) (by intro d hd; cases hd)))
def cl_30406 : CNF.NClause := [(81,true),(23,false),(1,true),(28,false),(9,false)]
theorem der_30406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30406 :=
  CNF.rup_sound cl_30406 [cl_24338,cl_30350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24338 v h) (hints_cons _ _ _ (der_30350 v h) (by intro d hd; cases hd)))
def cl_30407 : CNF.NClause := [(28,true),(81,true),(15,true),(9,false),(23,false)]
theorem der_30407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30407 :=
  CNF.rup_sound cl_30407 [cl_24339,cl_30396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24339 v h) (hints_cons _ _ _ (der_30396 v h) (by intro d hd; cases hd)))
def cl_30408 : CNF.NClause := [(78,true),(15,true),(6,true),(27,false),(22,false)]
theorem der_30408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30408 :=
  CNF.rup_sound cl_30408 [cl_24340,cl_30192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24340 v h) (hints_cons _ _ _ (der_30192 v h) (by intro d hd; cases hd)))
def cl_30409 : CNF.NClause := [(78,true),(6,true),(15,true),(4,false),(22,false)]
theorem der_30409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30409 :=
  CNF.rup_sound cl_30409 [cl_24341,cl_30408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24341 v h) (hints_cons _ _ _ (der_30408 v h) (by intro d hd; cases hd)))
def cl_30410 : CNF.NClause := [(78,true),(15,true),(6,true),(4,false),(27,false)]
theorem der_30410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30410 :=
  CNF.rup_sound cl_30410 [cl_24342,cl_30408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24342 v h) (hints_cons _ _ _ (der_30408 v h) (by intro d hd; cases hd)))
def cl_30411 : CNF.NClause := [(9,false),(12,true),(1,true),(28,false),(81,true)]
theorem der_30411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30411 :=
  CNF.rup_sound cl_30411 [cl_24343,cl_30406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24343 v h) (hints_cons _ _ _ (der_30406 v h) (by intro d hd; cases hd)))
def cl_30412 : CNF.NClause := [(2,true),(26,false),(14,true),(21,false),(79,true)]
theorem der_30412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30412 :=
  CNF.rup_sound cl_30412 [cl_24344,cl_29816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24344 v h) (hints_cons _ _ _ (der_29816 v h) (by intro d hd; cases hd)))
def cl_30413 : CNF.NClause := [(15,true),(24,false),(29,false),(80,true),(7,true)]
theorem der_30413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30413 :=
  CNF.rup_sound cl_30413 [cl_24345,cl_24337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24345 v h) (hints_cons _ _ _ (der_24337 v h) (by intro d hd; cases hd)))
def cl_30414 : CNF.NClause := [(80,true),(11,false),(7,true),(15,true),(29,false)]
theorem der_30414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30414 :=
  CNF.rup_sound cl_30414 [cl_24346,cl_30413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24346 v h) (hints_cons _ _ _ (der_30413 v h) (by intro d hd; cases hd)))
def cl_30415 : CNF.NClause := [(29,true),(11,false),(24,false),(80,true),(7,true)]
theorem der_30415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30415 :=
  CNF.rup_sound cl_30415 [cl_24347,cl_24302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24347 v h) (hints_cons _ _ _ (der_24302 v h) (by intro d hd; cases hd)))
def cl_30416 : CNF.NClause := [(79,true),(26,true),(2,true),(14,false),(21,false)]
theorem der_30416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30416 :=
  CNF.rup_sound cl_30416 [cl_24348,cl_23571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24348 v h) (hints_cons _ _ _ (der_23571 v h) (by intro d hd; cases hd)))
def cl_30418 : CNF.NClause := [(78,true),(27,false),(15,true),(4,true),(13,false)]
theorem der_30418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30418 :=
  CNF.rup_sound cl_30418 [cl_24350,cl_30195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24350 v h) (hints_cons _ _ _ (der_30195 v h) (by intro d hd; cases hd)))
def cl_30419 : CNF.NClause := [(4,true),(78,true),(13,false),(27,true),(22,false)]
theorem der_30419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30419 :=
  CNF.rup_sound cl_30419 [cl_24351,cl_30198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24351 v h) (hints_cons _ _ _ (der_30198 v h) (by intro d hd; cases hd)))
def cl_30420 : CNF.NClause := [(9,true),(28,false),(15,true),(23,false),(81,true)]
theorem der_30420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30420 :=
  CNF.rup_sound cl_30420 [cl_24352,cl_30325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24352 v h) (hints_cons _ _ _ (der_30325 v h) (by intro d hd; cases hd)))
def cl_30421 : CNF.NClause := [(28,false),(15,true),(9,true),(1,false),(81,true)]
theorem der_30421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30421 :=
  CNF.rup_sound cl_30421 [cl_24353,cl_30420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24353 v h) (hints_cons _ _ _ (der_30420 v h) (by intro d hd; cases hd)))
def cl_30422 : CNF.NClause := [(81,true),(9,true),(28,true),(23,false),(1,false)]
theorem der_30422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30422 :=
  CNF.rup_sound cl_30422 [cl_24354,cl_23570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24354 v h) (hints_cons _ _ _ (der_23570 v h) (by intro d hd; cases hd)))
def cl_30423 : CNF.NClause := [(26,false),(11,true),(23,false),(5,false),(83,true)]
theorem der_30423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30423 :=
  CNF.rup_sound cl_30423 [cl_24356,cl_24355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24356 v h) (hints_cons _ _ _ (der_24355 v h) (by intro d hd; cases hd)))
def cl_30424 : CNF.NClause := [(26,false),(11,true),(17,false),(5,false),(83,true)]
theorem der_30424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30424 :=
  CNF.rup_sound cl_30424 [cl_24357,cl_30423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24357 v h) (hints_cons _ _ _ (der_30423 v h) (by intro d hd; cases hd)))
def cl_30425 : CNF.NClause := [(23,true),(83,true),(11,true),(26,false),(5,false)]
theorem der_30425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30425 :=
  CNF.rup_sound cl_30425 [cl_24358,cl_30424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24358 v h) (hints_cons _ _ _ (der_30424 v h) (by intro d hd; cases hd)))
def cl_30426 : CNF.NClause := [(26,true),(17,false),(4,false),(23,false),(83,true)]
theorem der_30426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30426 :=
  CNF.rup_sound cl_30426 [cl_24359,cl_30341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24359 v h) (hints_cons _ _ _ (der_30341 v h) (by intro d hd; cases hd)))
def cl_30427 : CNF.NClause := [(83,true),(17,true),(23,false),(11,true),(5,false)]
theorem der_30427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30427 :=
  CNF.rup_sound cl_30427 [cl_24360,cl_30423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24360 v h) (hints_cons _ _ _ (der_30423 v h) (by intro d hd; cases hd)))
def cl_30428 : CNF.NClause := [(23,true),(83,true),(26,true),(4,false),(17,false)]
theorem der_30428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30428 :=
  CNF.rup_sound cl_30428 [cl_24361,cl_30343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24361 v h) (hints_cons _ _ _ (der_30343 v h) (by intro d hd; cases hd)))
def cl_30429 : CNF.NClause := [(23,true),(5,false),(11,true),(4,false),(83,true)]
theorem der_30429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30429 :=
  CNF.rup_sound cl_30429 [cl_24362,cl_30425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24362 v h) (hints_cons _ _ _ (der_30425 v h) (by intro d hd; cases hd)))
def cl_30430 : CNF.NClause := [(80,true),(3,false),(15,false),(24,false),(29,false)]
theorem der_30430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30430 :=
  CNF.rup_sound cl_30430 [cl_24363,cl_24147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24363 v h) (hints_cons _ _ _ (der_24147 v h) (by intro d hd; cases hd)))
def cl_30432 : CNF.NClause := [(80,true),(11,true),(15,false),(3,false),(29,false)]
theorem der_30432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30432 :=
  CNF.rup_sound cl_30432 [cl_24365,cl_30430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24365 v h) (hints_cons _ _ _ (der_30430 v h) (by intro d hd; cases hd)))
def cl_30433 : CNF.NClause := [(80,true),(24,true),(15,true),(3,false),(29,false)]
theorem der_30433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30433 :=
  CNF.rup_sound cl_30433 [cl_24366,cl_30387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24366 v h) (hints_cons _ _ _ (der_30387 v h) (by intro d hd; cases hd)))
def cl_30434 : CNF.NClause := [(29,true),(15,false),(80,true),(3,false),(24,false)]
theorem der_30434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30434 :=
  CNF.rup_sound cl_30434 [cl_24367,cl_30259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24367 v h) (hints_cons _ _ _ (der_30259 v h) (by intro d hd; cases hd)))
def cl_30435 : CNF.NClause := [(11,true),(24,false),(80,true),(3,false),(15,true)]
theorem der_30435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30435 :=
  CNF.rup_sound cl_30435 [cl_24368,cl_30261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24368 v h) (hints_cons _ _ _ (der_30261 v h) (by intro d hd; cases hd)))
def cl_30436 : CNF.NClause := [(80,true),(29,true),(15,false),(3,false),(7,false)]
theorem der_30436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30436 :=
  CNF.rup_sound cl_30436 [cl_24369,cl_30434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24369 v h) (hints_cons _ _ _ (der_30434 v h) (by intro d hd; cases hd)))
def cl_30437 : CNF.NClause := [(80,true),(29,true),(15,true),(3,false),(7,false)]
theorem der_30437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30437 :=
  CNF.rup_sound cl_30437 [cl_24370,cl_30389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24370 v h) (hints_cons _ _ _ (der_30389 v h) (by intro d hd; cases hd)))
def cl_30438 : CNF.NClause := [(69,true),(9,false),(20,false),(27,false),(18,true)]
theorem der_30438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30438 :=
  CNF.rup_sound cl_30438 [cl_24372,cl_30027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24372 v h) (hints_cons _ _ _ (der_30027 v h) (by intro d hd; cases hd)))
def cl_30439 : CNF.NClause := [(69,true),(27,false),(9,false),(18,false),(2,false)]
theorem der_30439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30439 :=
  CNF.rup_sound cl_30439 [cl_24373,cl_24371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24373 v h) (hints_cons _ _ _ (der_24371 v h) (by intro d hd; cases hd)))
def cl_30440 : CNF.NClause := [(27,false),(20,true),(9,false),(69,true),(18,true)]
theorem der_30440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30440 :=
  CNF.rup_sound cl_30440 [cl_24374,cl_23583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24374 v h) (hints_cons _ _ _ (der_23583 v h) (by intro d hd; cases hd)))
def cl_30441 : CNF.NClause := [(69,true),(20,false),(9,false),(18,false),(2,false)]
theorem der_30441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30441 :=
  CNF.rup_sound cl_30441 [cl_24375,cl_24371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24375 v h) (hints_cons _ _ _ (der_24371 v h) (by intro d hd; cases hd)))
def cl_30443 : CNF.NClause := [(69,true),(2,false),(9,false),(18,false),(11,true)]
theorem der_30443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30443 :=
  CNF.rup_sound cl_30443 [cl_24377,cl_30439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24377 v h) (hints_cons _ _ _ (der_30439 v h) (by intro d hd; cases hd)))
def cl_30444 : CNF.NClause := [(69,true),(27,true),(11,true),(9,false),(2,false)]
theorem der_30444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30444 :=
  CNF.rup_sound cl_30444 [cl_24378,cl_30443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24378 v h) (hints_cons _ _ _ (der_30443 v h) (by intro d hd; cases hd)))
def cl_30445 : CNF.NClause := [(69,true),(2,true),(20,false),(27,false),(9,false)]
theorem der_30445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30445 :=
  CNF.rup_sound cl_30445 [cl_24379,cl_30363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24379 v h) (hints_cons _ _ _ (der_30363 v h) (by intro d hd; cases hd)))
def cl_30446 : CNF.NClause := [(69,true),(27,false),(2,true),(20,true),(9,false)]
theorem der_30446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30446 :=
  CNF.rup_sound cl_30446 [cl_24380,cl_24173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24380 v h) (hints_cons _ _ _ (der_24173 v h) (by intro d hd; cases hd)))
def cl_30447 : CNF.NClause := [(69,true),(27,true),(2,true),(20,false),(9,false)]
theorem der_30447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30447 :=
  CNF.rup_sound cl_30447 [cl_24381,cl_30338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24381 v h) (hints_cons _ _ _ (der_30338 v h) (by intro d hd; cases hd)))
def cl_30448 : CNF.NClause := [(69,true),(20,true),(2,true),(9,false),(18,false)]
theorem der_30448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30448 :=
  CNF.rup_sound cl_30448 [cl_24382,cl_30446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24382 v h) (hints_cons _ _ _ (der_30446 v h) (by intro d hd; cases hd)))
def cl_30449 : CNF.NClause := [(80,true),(29,false),(24,false),(7,true),(11,true)]
theorem der_30449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30449 :=
  CNF.rup_sound cl_30449 [cl_24383,cl_30413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24383 v h) (hints_cons _ _ _ (der_30413 v h) (by intro d hd; cases hd)))
def cl_30450 : CNF.NClause := [(29,false),(11,true),(15,false),(80,true),(7,true)]
theorem der_30450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30450 :=
  CNF.rup_sound cl_30450 [cl_24384,cl_30449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24384 v h) (hints_cons _ _ _ (der_30449 v h) (by intro d hd; cases hd)))
def cl_30451 : CNF.NClause := [(80,true),(29,true),(15,false),(24,false),(7,true)]
theorem der_30451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30451 :=
  CNF.rup_sound cl_30451 [cl_24385,cl_30434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24385 v h) (hints_cons _ _ _ (der_30434 v h) (by intro d hd; cases hd)))
def cl_30452 : CNF.NClause := [(69,true),(27,false),(11,true),(20,false),(2,true)]
theorem der_30452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30452 :=
  CNF.rup_sound cl_30452 [cl_24387,cl_24386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24387 v h) (hints_cons _ _ _ (der_24386 v h) (by intro d hd; cases hd)))
def cl_30453 : CNF.NClause := [(69,true),(27,true),(18,false),(20,false),(2,true)]
theorem der_30453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30453 :=
  CNF.rup_sound cl_30453 [cl_24389,cl_30447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24389 v h) (hints_cons _ _ _ (der_30447 v h) (by intro d hd; cases hd)))
def cl_30454 : CNF.NClause := [(70,true),(6,true),(17,false),(28,false),(14,false)]
theorem der_30454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30454 :=
  CNF.rup_sound cl_30454 [cl_24390,cl_30271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24390 v h) (hints_cons _ _ _ (der_30271 v h) (by intro d hd; cases hd)))
def cl_30455 : CNF.NClause := [(3,true),(9,false),(75,true),(10,false),(22,false)]
theorem der_30455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30455 :=
  CNF.rup_sound cl_30455 [cl_24391,cl_24275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24391 v h) (hints_cons _ _ _ (der_24275 v h) (by intro d hd; cases hd)))
def cl_30456 : CNF.NClause := [(7,false),(15,false),(80,true),(29,false),(24,false)]
theorem der_30456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30456 :=
  CNF.rup_sound cl_30456 [cl_24393,cl_30430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24393 v h) (hints_cons _ _ _ (der_30430 v h) (by intro d hd; cases hd)))
def cl_30459 : CNF.NClause := [(80,true),(11,false),(24,true),(15,false),(29,false)]
theorem der_30459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30459 :=
  CNF.rup_sound cl_30459 [cl_24396,cl_30375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24396 v h) (hints_cons _ _ _ (der_30375 v h) (by intro d hd; cases hd)))
def cl_30460 : CNF.NClause := [(80,true),(29,false),(11,true),(24,true),(15,false)]
theorem der_30460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30460 :=
  CNF.rup_sound cl_30460 [cl_24397,cl_30432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24397 v h) (hints_cons _ _ _ (der_30432 v h) (by intro d hd; cases hd)))
def cl_30461 : CNF.NClause := [(80,true),(11,false),(15,true),(3,true),(29,false)]
theorem der_30461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30461 :=
  CNF.rup_sound cl_30461 [cl_24398,cl_30414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24398 v h) (hints_cons _ _ _ (der_30414 v h) (by intro d hd; cases hd)))
def cl_30462 : CNF.NClause := [(80,true),(29,false),(15,true),(3,true),(7,false)]
theorem der_30462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30462 :=
  CNF.rup_sound cl_30462 [cl_24399,cl_30461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24399 v h) (hints_cons _ _ _ (der_30461 v h) (by intro d hd; cases hd)))
def cl_30463 : CNF.NClause := [(29,true),(80,true),(15,false),(24,false),(11,false)]
theorem der_30463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30463 :=
  CNF.rup_sound cl_30463 [cl_24400,cl_30451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24400 v h) (hints_cons _ _ _ (der_30451 v h) (by intro d hd; cases hd)))
def cl_30464 : CNF.NClause := [(7,false),(3,true),(24,false),(80,true),(15,true)]
theorem der_30464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30464 :=
  CNF.rup_sound cl_30464 [cl_24403,cl_30462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24403 v h) (hints_cons _ _ _ (der_30462 v h) (by intro d hd; cases hd)))
def cl_30465 : CNF.NClause := [(80,true),(11,false),(15,false),(24,true),(29,true)]
theorem der_30465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30465 :=
  CNF.rup_sound cl_30465 [cl_24404,cl_30382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24404 v h) (hints_cons _ _ _ (der_30382 v h) (by intro d hd; cases hd)))
def cl_30466 : CNF.NClause := [(80,true),(24,true),(29,true),(15,false),(7,false)]
theorem der_30466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30466 :=
  CNF.rup_sound cl_30466 [cl_24405,cl_30465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24405 v h) (hints_cons _ _ _ (der_30465 v h) (by intro d hd; cases hd)))
def cl_30467 : CNF.NClause := [(11,false),(80,true),(29,true),(15,true),(7,false)]
theorem der_30467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30467 :=
  CNF.rup_sound cl_30467 [cl_24406,cl_30437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24406 v h) (hints_cons _ _ _ (der_30437 v h) (by intro d hd; cases hd)))
def cl_30468 : CNF.NClause := [(70,true),(14,false),(17,false),(28,false),(20,false)]
theorem der_30468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30468 :=
  CNF.rup_sound cl_30468 [cl_24407,cl_30454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24407 v h) (hints_cons _ _ _ (der_30454 v h) (by intro d hd; cases hd)))
def cl_30469 : CNF.NClause := [(6,false),(17,false),(70,true),(20,false),(28,false)]
theorem der_30469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30469 :=
  CNF.rup_sound cl_30469 [cl_24408,cl_30468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24408 v h) (hints_cons _ _ _ (der_30468 v h) (by intro d hd; cases hd)))
def cl_30470 : CNF.NClause := [(14,true),(28,false),(17,true),(70,true),(20,false)]
theorem der_30470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30470 :=
  CNF.rup_sound cl_30470 [cl_24410,cl_29832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24410 v h) (hints_cons _ _ _ (der_29832 v h) (by intro d hd; cases hd)))
def cl_30473 : CNF.NClause := [(70,true),(14,false),(6,false),(28,false),(3,true)]
theorem der_30473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30473 :=
  CNF.rup_sound cl_30473 [cl_24413,cl_24409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24413 v h) (hints_cons _ _ _ (der_24409 v h) (by intro d hd; cases hd)))
def cl_30474 : CNF.NClause := [(20,true),(3,true),(28,false),(6,false),(70,true)]
theorem der_30474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30474 :=
  CNF.rup_sound cl_30474 [cl_24414,cl_30473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24414 v h) (hints_cons _ _ _ (der_30473 v h) (by intro d hd; cases hd)))
def cl_30475 : CNF.NClause := [(6,false),(14,true),(70,true),(20,false),(17,false)]
theorem der_30475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30475 :=
  CNF.rup_sound cl_30475 [cl_24416,cl_30469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24416 v h) (hints_cons _ _ _ (der_30469 v h) (by intro d hd; cases hd)))
def cl_30476 : CNF.NClause := [(70,true),(14,false),(6,false),(20,false),(3,true)]
theorem der_30476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30476 :=
  CNF.rup_sound cl_30476 [cl_24417,cl_24415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24417 v h) (hints_cons _ _ _ (der_24415 v h) (by intro d hd; cases hd)))
def cl_30477 : CNF.NClause := [(6,false),(14,true),(17,true),(70,true),(20,false)]
theorem der_30477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30477 :=
  CNF.rup_sound cl_30477 [cl_24418,cl_30470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24418 v h) (hints_cons _ _ _ (der_30470 v h) (by intro d hd; cases hd)))
def cl_30478 : CNF.NClause := [(70,true),(14,false),(17,false),(20,true),(3,true)]
theorem der_30478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30478 :=
  CNF.rup_sound cl_30478 [cl_24419,cl_30272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24419 v h) (hints_cons _ _ _ (der_30272 v h) (by intro d hd; cases hd)))
def cl_30479 : CNF.NClause := [(28,true),(6,false),(14,true),(70,true),(17,false)]
theorem der_30479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30479 :=
  CNF.rup_sound cl_30479 [cl_24420,cl_30475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24420 v h) (hints_cons _ _ _ (der_30475 v h) (by intro d hd; cases hd)))
def cl_30480 : CNF.NClause := [(70,true),(14,false),(3,true),(17,true),(6,false)]
theorem der_30480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30480 :=
  CNF.rup_sound cl_30480 [cl_24421,cl_30476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24421 v h) (hints_cons _ _ _ (der_30476 v h) (by intro d hd; cases hd)))
def cl_30481 : CNF.NClause := [(85,true),(27,false),(19,false),(3,true),(21,false)]
theorem der_30481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30481 :=
  CNF.rup_sound cl_30481 [cl_24423,cl_24422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24423 v h) (hints_cons _ _ _ (der_24422 v h) (by intro d hd; cases hd)))
def cl_30483 : CNF.NClause := [(27,false),(3,true),(5,false),(85,true),(21,false)]
theorem der_30483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30483 :=
  CNF.rup_sound cl_30483 [cl_24425,cl_30481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24425 v h) (hints_cons _ _ _ (der_30481 v h) (by intro d hd; cases hd)))
def cl_30484 : CNF.NClause := [(85,true),(21,true),(27,false),(12,false),(19,false)]
theorem der_30484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30484 :=
  CNF.rup_sound cl_30484 [cl_24426,cl_30232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24426 v h) (hints_cons _ _ _ (der_30232 v h) (by intro d hd; cases hd)))
def cl_30485 : CNF.NClause := [(85,true),(19,false),(5,false),(27,false),(21,true)]
theorem der_30485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30485 :=
  CNF.rup_sound cl_30485 [cl_24427,cl_30484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24427 v h) (hints_cons _ _ _ (der_30484 v h) (by intro d hd; cases hd)))
def cl_30486 : CNF.NClause := [(27,false),(85,true),(19,true),(3,true),(12,false)]
theorem der_30486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30486 :=
  CNF.rup_sound cl_30486 [cl_24428,cl_30233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24428 v h) (hints_cons _ _ _ (der_30233 v h) (by intro d hd; cases hd)))
def cl_30487 : CNF.NClause := [(85,true),(27,false),(5,false),(21,true),(12,true)]
theorem der_30487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30487 :=
  CNF.rup_sound cl_30487 [cl_24429,cl_30485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24429 v h) (hints_cons _ _ _ (der_30485 v h) (by intro d hd; cases hd)))
def cl_30488 : CNF.NClause := [(85,true),(27,true),(12,false),(19,false),(21,false)]
theorem der_30488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30488 :=
  CNF.rup_sound cl_30488 [cl_24430,cl_30234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24430 v h) (hints_cons _ _ _ (der_30234 v h) (by intro d hd; cases hd)))
def cl_30489 : CNF.NClause := [(3,true),(85,true),(12,true),(19,false),(21,false)]
theorem der_30489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30489 :=
  CNF.rup_sound cl_30489 [cl_24431,cl_30359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24431 v h) (hints_cons _ _ _ (der_30359 v h) (by intro d hd; cases hd)))
def cl_30490 : CNF.NClause := [(85,true),(3,true),(12,false),(19,true),(21,false)]
theorem der_30490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30490 :=
  CNF.rup_sound cl_30490 [cl_24432,cl_30235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24432 v h) (hints_cons _ _ _ (der_30235 v h) (by intro d hd; cases hd)))
def cl_30491 : CNF.NClause := [(85,true),(3,true),(5,false),(12,true),(21,false)]
theorem der_30491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30491 :=
  CNF.rup_sound cl_30491 [cl_24433,cl_30483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24433 v h) (hints_cons _ _ _ (der_30483 v h) (by intro d hd; cases hd)))
def cl_30492 : CNF.NClause := [(85,true),(19,false),(5,false),(21,true),(12,false)]
theorem der_30492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30492 :=
  CNF.rup_sound cl_30492 [cl_24434,cl_30485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24434 v h) (hints_cons _ _ _ (der_30485 v h) (by intro d hd; cases hd)))
def cl_30493 : CNF.NClause := [(85,true),(21,true),(12,true),(5,false),(19,false)]
theorem der_30493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30493 :=
  CNF.rup_sound cl_30493 [cl_24435,cl_30487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24435 v h) (hints_cons _ _ _ (der_30487 v h) (by intro d hd; cases hd)))
def cl_30494 : CNF.NClause := [(12,false),(21,true),(27,true),(5,false),(85,true)]
theorem der_30494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30494 :=
  CNF.rup_sound cl_30494 [cl_24436,cl_30492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24436 v h) (hints_cons _ _ _ (der_30492 v h) (by intro d hd; cases hd)))
def cl_30495 : CNF.NClause := [(75,true),(3,true),(10,false),(26,false),(22,false)]
theorem der_30495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30495 :=
  CNF.rup_sound cl_30495 [cl_24439,cl_24437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24439 v h) (hints_cons _ _ _ (der_24437 v h) (by intro d hd; cases hd)))
def cl_30496 : CNF.NClause := [(75,true),(9,true),(3,true),(26,false),(22,false)]
theorem der_30496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30496 :=
  CNF.rup_sound cl_30496 [cl_24440,cl_30495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24440 v h) (hints_cons _ _ _ (der_30495 v h) (by intro d hd; cases hd)))
def cl_30497 : CNF.NClause := [(75,true),(3,true),(10,false),(26,false),(16,false)]
theorem der_30497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30497 :=
  CNF.rup_sound cl_30497 [cl_24441,cl_30495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24441 v h) (hints_cons _ _ _ (der_30495 v h) (by intro d hd; cases hd)))
def cl_30498 : CNF.NClause := [(75,true),(9,true),(3,true),(26,false),(16,false)]
theorem der_30498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30498 :=
  CNF.rup_sound cl_30498 [cl_24442,cl_30497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24442 v h) (hints_cons _ _ _ (der_30497 v h) (by intro d hd; cases hd)))
def cl_30499 : CNF.NClause := [(22,true),(10,false),(3,true),(26,false),(75,true)]
theorem der_30499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30499 :=
  CNF.rup_sound cl_30499 [cl_24443,cl_30497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24443 v h) (hints_cons _ _ _ (der_30497 v h) (by intro d hd; cases hd)))
def cl_30500 : CNF.NClause := [(3,true),(16,false),(10,false),(75,true),(22,false)]
theorem der_30500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30500 :=
  CNF.rup_sound cl_30500 [cl_24444,cl_24437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24444 v h) (hints_cons _ _ _ (der_24437 v h) (by intro d hd; cases hd)))
def cl_30501 : CNF.NClause := [(75,true),(16,false),(3,true),(22,false),(9,true)]
theorem der_30501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30501 :=
  CNF.rup_sound cl_30501 [cl_24445,cl_30500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24445 v h) (hints_cons _ _ _ (der_30500 v h) (by intro d hd; cases hd)))
def cl_30502 : CNF.NClause := [(75,true),(3,true),(16,true),(10,false),(22,false)]
theorem der_30502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30502 :=
  CNF.rup_sound cl_30502 [cl_24446,cl_30495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24446 v h) (hints_cons _ _ _ (der_30495 v h) (by intro d hd; cases hd)))
def cl_30503 : CNF.NClause := [(75,true),(9,true),(3,true),(10,false),(16,false)]
theorem der_30503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30503 :=
  CNF.rup_sound cl_30503 [cl_24447,cl_30501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24447 v h) (hints_cons _ _ _ (der_30501 v h) (by intro d hd; cases hd)))
def cl_30504 : CNF.NClause := [(75,true),(3,true),(10,false),(22,true),(9,false)]
theorem der_30504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30504 :=
  CNF.rup_sound cl_30504 [cl_24448,cl_24271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24448 v h) (hints_cons _ _ _ (der_24271 v h) (by intro d hd; cases hd)))
def cl_30505 : CNF.NClause := [(70,true),(6,true),(14,false),(3,true),(17,false)]
theorem der_30505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30505 :=
  CNF.rup_sound cl_30505 [cl_24449,cl_30272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24449 v h) (hints_cons _ _ _ (der_30272 v h) (by intro d hd; cases hd)))
def cl_30506 : CNF.NClause := [(80,true),(11,false),(7,true),(15,false),(24,false)]
theorem der_30506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30506 :=
  CNF.rup_sound cl_30506 [cl_24450,cl_24302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24450 v h) (hints_cons _ _ _ (der_24302 v h) (by intro d hd; cases hd)))
def cl_30507 : CNF.NClause := [(6,false),(70,true),(20,false),(17,false),(3,false)]
theorem der_30507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30507 :=
  CNF.rup_sound cl_30507 [cl_24451,cl_30285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24451 v h) (hints_cons _ _ _ (der_30285 v h) (by intro d hd; cases hd)))
def cl_30508 : CNF.NClause := [(81,true),(28,true),(15,false),(23,false),(1,true)]
theorem der_30508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30508 :=
  CNF.rup_sound cl_30508 [cl_24452,cl_30329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24452 v h) (hints_cons _ _ _ (der_30329 v h) (by intro d hd; cases hd)))
def cl_30509 : CNF.NClause := [(84,true),(24,false),(5,false),(13,false),(16,false)]
theorem der_30509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30509 :=
  CNF.rup_sound cl_30509 [cl_24453,cl_23617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24453 v h) (hints_cons _ _ _ (der_23617 v h) (by intro d hd; cases hd)))
def cl_30510 : CNF.NClause := [(86,true),(29,true),(5,true),(14,false),(18,false)]
theorem der_30510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30510 :=
  CNF.rup_sound cl_30510 [cl_24454,cl_30369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24454 v h) (hints_cons _ _ _ (der_30369 v h) (by intro d hd; cases hd)))
def cl_30511 : CNF.NClause := [(29,true),(14,false),(86,true),(1,false),(18,false)]
theorem der_30511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30511 :=
  CNF.rup_sound cl_30511 [cl_24455,cl_30369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24455 v h) (hints_cons _ _ _ (der_30369 v h) (by intro d hd; cases hd)))
def cl_30512 : CNF.NClause := [(7,true),(18,false),(21,true),(73,true),(10,false)]
theorem der_30512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30512 :=
  CNF.rup_sound cl_30512 [cl_24456,cl_30035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24456 v h) (hints_cons _ _ _ (der_30035 v h) (by intro d hd; cases hd)))
def cl_30513 : CNF.NClause := [(21,true),(73,true),(10,false),(7,false),(18,false)]
theorem der_30513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30513 :=
  CNF.rup_sound cl_30513 [cl_24457,cl_29975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24457 v h) (hints_cons _ _ _ (der_29975 v h) (by intro d hd; cases hd)))
def cl_30514 : CNF.NClause := [(74,true),(19,false),(23,false),(29,false),(2,false)]
theorem der_30514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30514 :=
  CNF.rup_sound cl_30514 [cl_24458,cl_30162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24458 v h) (hints_cons _ _ _ (der_30162 v h) (by intro d hd; cases hd)))
def cl_30515 : CNF.NClause := [(74,true),(10,true),(23,false),(29,false),(2,false)]
theorem der_30515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30515 :=
  CNF.rup_sound cl_30515 [cl_24459,cl_30514] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24459 v h) (hints_cons _ _ _ (der_30514 v h) (by intro d hd; cases hd)))
def cl_30516 : CNF.NClause := [(74,true),(10,true),(19,false),(29,false),(2,false)]
theorem der_30516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30516 :=
  CNF.rup_sound cl_30516 [cl_24460,cl_30170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24460 v h) (hints_cons _ _ _ (der_30170 v h) (by intro d hd; cases hd)))
def cl_30517 : CNF.NClause := [(74,true),(29,true),(23,false),(19,false),(6,false)]
theorem der_30517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30517 :=
  CNF.rup_sound cl_30517 [cl_24462,cl_30370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24462 v h) (hints_cons _ _ _ (der_30370 v h) (by intro d hd; cases hd)))
def cl_30518 : CNF.NClause := [(74,true),(10,true),(29,true),(23,false),(6,false)]
theorem der_30518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30518 :=
  CNF.rup_sound cl_30518 [cl_24463,cl_30517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24463 v h) (hints_cons _ _ _ (der_30517 v h) (by intro d hd; cases hd)))
def cl_30519 : CNF.NClause := [(74,true),(29,true),(19,false),(6,false),(2,false)]
theorem der_30519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30519 :=
  CNF.rup_sound cl_30519 [cl_24464,cl_30517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24464 v h) (hints_cons _ _ _ (der_30517 v h) (by intro d hd; cases hd)))
def cl_30520 : CNF.NClause := [(73,true),(7,false),(21,false),(28,false),(18,false)]
theorem der_30520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30520 :=
  CNF.rup_sound cl_30520 [cl_24466,cl_23536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24466 v h) (hints_cons _ _ _ (der_23536 v h) (by intro d hd; cases hd)))
def cl_30521 : CNF.NClause := [(73,true),(4,false),(28,false),(7,false),(21,false)]
theorem der_30521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30521 :=
  CNF.rup_sound cl_30521 [cl_24467,cl_29805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24467 v h) (hints_cons _ _ _ (der_29805 v h) (by intro d hd; cases hd)))
def cl_30522 : CNF.NClause := [(21,true),(73,true),(7,false),(18,false),(28,false)]
theorem der_30522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_30522 :=
  CNF.rup_sound cl_30522 [cl_24468,cl_29975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24468 v h) (hints_cons _ _ _ (der_29975 v h) (by intro d hd; cases hd)))
def chunk015 : List CNF.NClause := [cl_29960,cl_29961,cl_29962,cl_29963,cl_29964,cl_29965,cl_29967,cl_29968,cl_29969,cl_29970,cl_29971,cl_29972,cl_29973,cl_29974,cl_29975,cl_29976,cl_29977,cl_29980,cl_29981,cl_29982,cl_29983,cl_29984,cl_29986,cl_29987,cl_29988,cl_29989,cl_29990,cl_29991,cl_29992,cl_29993,cl_29994,cl_29995,cl_29996,cl_29998,cl_29999,cl_30000,cl_30001,cl_30002,cl_30003,cl_30004,cl_30005,cl_30006,cl_30007,cl_30008,cl_30009,cl_30010,cl_30011,cl_30014,cl_30015,cl_30016,cl_30017,cl_30018,cl_30020,cl_30021,cl_30022,cl_30024,cl_30025,cl_30026,cl_30027,cl_30029,cl_30031,cl_30032,cl_30033,cl_30034,cl_30035,cl_30036,cl_30037,cl_30038,cl_30039,cl_30040,cl_30042,cl_30045,cl_30046,cl_30047,cl_30048,cl_30050,cl_30051,cl_30052,cl_30053,cl_30055,cl_30056,cl_30057,cl_30058,cl_30059,cl_30060,cl_30061,cl_30062,cl_30063,cl_30064,cl_30065,cl_30066,cl_30067,cl_30068,cl_30069,cl_30070,cl_30072,cl_30074,cl_30075,cl_30076,cl_30077,cl_30078,cl_30079,cl_30080,cl_30081,cl_30082,cl_30084,cl_30085,cl_30087,cl_30088,cl_30089,cl_30090,cl_30091,cl_30093,cl_30094,cl_30095,cl_30096,cl_30097,cl_30099,cl_30100,cl_30101,cl_30102,cl_30103,cl_30104,cl_30105,cl_30106,cl_30107,cl_30108,cl_30109,cl_30110,cl_30111,cl_30113,cl_30114,cl_30115,cl_30116,cl_30117,cl_30119,cl_30120,cl_30121,cl_30122,cl_30123,cl_30124,cl_30125,cl_30126,cl_30127,cl_30128,cl_30129,cl_30130,cl_30131,cl_30132,cl_30133,cl_30134,cl_30135,cl_30136,cl_30137,cl_30138,cl_30139,cl_30140,cl_30141,cl_30142,cl_30143,cl_30144,cl_30145,cl_30146,cl_30147,cl_30148,cl_30149,cl_30150,cl_30151,cl_30152,cl_30154,cl_30155,cl_30156,cl_30158,cl_30159,cl_30160,cl_30162,cl_30163,cl_30164,cl_30165,cl_30166,cl_30167,cl_30168,cl_30169,cl_30170,cl_30171,cl_30172,cl_30173,cl_30174,cl_30175,cl_30176,cl_30177,cl_30178,cl_30179,cl_30180,cl_30181,cl_30182,cl_30183,cl_30184,cl_30185,cl_30187,cl_30188,cl_30189,cl_30190,cl_30191,cl_30192,cl_30194,cl_30195,cl_30196,cl_30197,cl_30198,cl_30199,cl_30200,cl_30201,cl_30202,cl_30203,cl_30204,cl_30205,cl_30206,cl_30208,cl_30209,cl_30210,cl_30211,cl_30212,cl_30213,cl_30215,cl_30216,cl_30217,cl_30218,cl_30219,cl_30220,cl_30221,cl_30222,cl_30223,cl_30224,cl_30225,cl_30226,cl_30227,cl_30228,cl_30229,cl_30230,cl_30231,cl_30232,cl_30233,cl_30234,cl_30235,cl_30236,cl_30237,cl_30238,cl_30240,cl_30241,cl_30242,cl_30243,cl_30244,cl_30245,cl_30246,cl_30248,cl_30249,cl_30250,cl_30251,cl_30252,cl_30253,cl_30259,cl_30260,cl_30261,cl_30262,cl_30263,cl_30264,cl_30265,cl_30266,cl_30267,cl_30268,cl_30270,cl_30271,cl_30272,cl_30273,cl_30274,cl_30276,cl_30277,cl_30278,cl_30279,cl_30280,cl_30281,cl_30282,cl_30283,cl_30284,cl_30285,cl_30286,cl_30287,cl_30289,cl_30290,cl_30291,cl_30293,cl_30295,cl_30296,cl_30297,cl_30299,cl_30300,cl_30301,cl_30302,cl_30303,cl_30304,cl_30306,cl_30307,cl_30309,cl_30310,cl_30311,cl_30313,cl_30314,cl_30315,cl_30316,cl_30317,cl_30318,cl_30319,cl_30321,cl_30322,cl_30323,cl_30324,cl_30325,cl_30326,cl_30327,cl_30328,cl_30329,cl_30330,cl_30331,cl_30332,cl_30333,cl_30334,cl_30336,cl_30337,cl_30338,cl_30339,cl_30341,cl_30343,cl_30344,cl_30345,cl_30346,cl_30347,cl_30348,cl_30349,cl_30350,cl_30351,cl_30352,cl_30353,cl_30354,cl_30355,cl_30356,cl_30358,cl_30359,cl_30360,cl_30361,cl_30362,cl_30363,cl_30364,cl_30365,cl_30366,cl_30367,cl_30368,cl_30369,cl_30370,cl_30371,cl_30372,cl_30373,cl_30374,cl_30375,cl_30376,cl_30377,cl_30378,cl_30379,cl_30380,cl_30381,cl_30382,cl_30384,cl_30385,cl_30386,cl_30387,cl_30388,cl_30389,cl_30390,cl_30391,cl_30392,cl_30393,cl_30394,cl_30395,cl_30396,cl_30397,cl_30399,cl_30400,cl_30401,cl_30402,cl_30403,cl_30405,cl_30406,cl_30407,cl_30408,cl_30409,cl_30410,cl_30411,cl_30412,cl_30413,cl_30414,cl_30415,cl_30416,cl_30418,cl_30419,cl_30420,cl_30421,cl_30422,cl_30423,cl_30424,cl_30425,cl_30426,cl_30427,cl_30428,cl_30429,cl_30430,cl_30432,cl_30433,cl_30434,cl_30435,cl_30436,cl_30437,cl_30438,cl_30439,cl_30440,cl_30441,cl_30443,cl_30444,cl_30445,cl_30446,cl_30447,cl_30448,cl_30449,cl_30450,cl_30451,cl_30452,cl_30453,cl_30454,cl_30455,cl_30456,cl_30459,cl_30460,cl_30461,cl_30462,cl_30463,cl_30464,cl_30465,cl_30466,cl_30467,cl_30468,cl_30469,cl_30470,cl_30473,cl_30474,cl_30475,cl_30476,cl_30477,cl_30478,cl_30479,cl_30480,cl_30481,cl_30483,cl_30484,cl_30485,cl_30486,cl_30487,cl_30488,cl_30489,cl_30490,cl_30491,cl_30492,cl_30493,cl_30494,cl_30495,cl_30496,cl_30497,cl_30498,cl_30499,cl_30500,cl_30501,cl_30502,cl_30503,cl_30504,cl_30505,cl_30506,cl_30507,cl_30508,cl_30509,cl_30510,cl_30511,cl_30512,cl_30513,cl_30514,cl_30515,cl_30516,cl_30517,cl_30518,cl_30519,cl_30520,cl_30521,cl_30522]
theorem chunk_sound015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk015, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_29960 v h) (hints_cons _ _ _ (der_29961 v h) (hints_cons _ _ _ (der_29962 v h) (hints_cons _ _ _ (der_29963 v h) (hints_cons _ _ _ (der_29964 v h) (hints_cons _ _ _ (der_29965 v h) (hints_cons _ _ _ (der_29967 v h) (hints_cons _ _ _ (der_29968 v h) (hints_cons _ _ _ (der_29969 v h) (hints_cons _ _ _ (der_29970 v h) (hints_cons _ _ _ (der_29971 v h) (hints_cons _ _ _ (der_29972 v h) (hints_cons _ _ _ (der_29973 v h) (hints_cons _ _ _ (der_29974 v h) (hints_cons _ _ _ (der_29975 v h) (hints_cons _ _ _ (der_29976 v h) (hints_cons _ _ _ (der_29977 v h) (hints_cons _ _ _ (der_29980 v h) (hints_cons _ _ _ (der_29981 v h) (hints_cons _ _ _ (der_29982 v h) (hints_cons _ _ _ (der_29983 v h) (hints_cons _ _ _ (der_29984 v h) (hints_cons _ _ _ (der_29986 v h) (hints_cons _ _ _ (der_29987 v h) (hints_cons _ _ _ (der_29988 v h) (hints_cons _ _ _ (der_29989 v h) (hints_cons _ _ _ (der_29990 v h) (hints_cons _ _ _ (der_29991 v h) (hints_cons _ _ _ (der_29992 v h) (hints_cons _ _ _ (der_29993 v h) (hints_cons _ _ _ (der_29994 v h) (hints_cons _ _ _ (der_29995 v h) (hints_cons _ _ _ (der_29996 v h) (hints_cons _ _ _ (der_29998 v h) (hints_cons _ _ _ (der_29999 v h) (hints_cons _ _ _ (der_30000 v h) (hints_cons _ _ _ (der_30001 v h) (hints_cons _ _ _ (der_30002 v h) (hints_cons _ _ _ (der_30003 v h) (hints_cons _ _ _ (der_30004 v h) (hints_cons _ _ _ (der_30005 v h) (hints_cons _ _ _ (der_30006 v h) (hints_cons _ _ _ (der_30007 v h) (hints_cons _ _ _ (der_30008 v h) (hints_cons _ _ _ (der_30009 v h) (hints_cons _ _ _ (der_30010 v h) (hints_cons _ _ _ (der_30011 v h) (hints_cons _ _ _ (der_30014 v h) (hints_cons _ _ _ (der_30015 v h) (hints_cons _ _ _ (der_30016 v h) (hints_cons _ _ _ (der_30017 v h) (hints_cons _ _ _ (der_30018 v h) (hints_cons _ _ _ (der_30020 v h) (hints_cons _ _ _ (der_30021 v h) (hints_cons _ _ _ (der_30022 v h) (hints_cons _ _ _ (der_30024 v h) (hints_cons _ _ _ (der_30025 v h) (hints_cons _ _ _ (der_30026 v h) (hints_cons _ _ _ (der_30027 v h) (hints_cons _ _ _ (der_30029 v h) (hints_cons _ _ _ (der_30031 v h) (hints_cons _ _ _ (der_30032 v h) (hints_cons _ _ _ (der_30033 v h) (hints_cons _ _ _ (der_30034 v h) (hints_cons _ _ _ (der_30035 v h) (hints_cons _ _ _ (der_30036 v h) (hints_cons _ _ _ (der_30037 v h) (hints_cons _ _ _ (der_30038 v h) (hints_cons _ _ _ (der_30039 v h) (hints_cons _ _ _ (der_30040 v h) (hints_cons _ _ _ (der_30042 v h) (hints_cons _ _ _ (der_30045 v h) (hints_cons _ _ _ (der_30046 v h) (hints_cons _ _ _ (der_30047 v h) (hints_cons _ _ _ (der_30048 v h) (hints_cons _ _ _ (der_30050 v h) (hints_cons _ _ _ (der_30051 v h) (hints_cons _ _ _ (der_30052 v h) (hints_cons _ _ _ (der_30053 v h) (hints_cons _ _ _ (der_30055 v h) (hints_cons _ _ _ (der_30056 v h) (hints_cons _ _ _ (der_30057 v h) (hints_cons _ _ _ (der_30058 v h) (hints_cons _ _ _ (der_30059 v h) (hints_cons _ _ _ (der_30060 v h) (hints_cons _ _ _ (der_30061 v h) (hints_cons _ _ _ (der_30062 v h) (hints_cons _ _ _ (der_30063 v h) (hints_cons _ _ _ (der_30064 v h) (hints_cons _ _ _ (der_30065 v h) (hints_cons _ _ _ (der_30066 v h) (hints_cons _ _ _ (der_30067 v h) (hints_cons _ _ _ (der_30068 v h) (hints_cons _ _ _ (der_30069 v h) (hints_cons _ _ _ (der_30070 v h) (hints_cons _ _ _ (der_30072 v h) (hints_cons _ _ _ (der_30074 v h) (hints_cons _ _ _ (der_30075 v h) (hints_cons _ _ _ (der_30076 v h) (hints_cons _ _ _ (der_30077 v h) (hints_cons _ _ _ (der_30078 v h) (hints_cons _ _ _ (der_30079 v h) (hints_cons _ _ _ (der_30080 v h) (hints_cons _ _ _ (der_30081 v h) (hints_cons _ _ _ (der_30082 v h) (hints_cons _ _ _ (der_30084 v h) (hints_cons _ _ _ (der_30085 v h) (hints_cons _ _ _ (der_30087 v h) (hints_cons _ _ _ (der_30088 v h) (hints_cons _ _ _ (der_30089 v h) (hints_cons _ _ _ (der_30090 v h) (hints_cons _ _ _ (der_30091 v h) (hints_cons _ _ _ (der_30093 v h) (hints_cons _ _ _ (der_30094 v h) (hints_cons _ _ _ (der_30095 v h) (hints_cons _ _ _ (der_30096 v h) (hints_cons _ _ _ (der_30097 v h) (hints_cons _ _ _ (der_30099 v h) (hints_cons _ _ _ (der_30100 v h) (hints_cons _ _ _ (der_30101 v h) (hints_cons _ _ _ (der_30102 v h) (hints_cons _ _ _ (der_30103 v h) (hints_cons _ _ _ (der_30104 v h) (hints_cons _ _ _ (der_30105 v h) (hints_cons _ _ _ (der_30106 v h) (hints_cons _ _ _ (der_30107 v h) (hints_cons _ _ _ (der_30108 v h) (hints_cons _ _ _ (der_30109 v h) (hints_cons _ _ _ (der_30110 v h) (hints_cons _ _ _ (der_30111 v h) (hints_cons _ _ _ (der_30113 v h) (hints_cons _ _ _ (der_30114 v h) (hints_cons _ _ _ (der_30115 v h) (hints_cons _ _ _ (der_30116 v h) (hints_cons _ _ _ (der_30117 v h) (hints_cons _ _ _ (der_30119 v h) (hints_cons _ _ _ (der_30120 v h) (hints_cons _ _ _ (der_30121 v h) (hints_cons _ _ _ (der_30122 v h) (hints_cons _ _ _ (der_30123 v h) (hints_cons _ _ _ (der_30124 v h) (hints_cons _ _ _ (der_30125 v h) (hints_cons _ _ _ (der_30126 v h) (hints_cons _ _ _ (der_30127 v h) (hints_cons _ _ _ (der_30128 v h) (hints_cons _ _ _ (der_30129 v h) (hints_cons _ _ _ (der_30130 v h) (hints_cons _ _ _ (der_30131 v h) (hints_cons _ _ _ (der_30132 v h) (hints_cons _ _ _ (der_30133 v h) (hints_cons _ _ _ (der_30134 v h) (hints_cons _ _ _ (der_30135 v h) (hints_cons _ _ _ (der_30136 v h) (hints_cons _ _ _ (der_30137 v h) (hints_cons _ _ _ (der_30138 v h) (hints_cons _ _ _ (der_30139 v h) (hints_cons _ _ _ (der_30140 v h) (hints_cons _ _ _ (der_30141 v h) (hints_cons _ _ _ (der_30142 v h) (hints_cons _ _ _ (der_30143 v h) (hints_cons _ _ _ (der_30144 v h) (hints_cons _ _ _ (der_30145 v h) (hints_cons _ _ _ (der_30146 v h) (hints_cons _ _ _ (der_30147 v h) (hints_cons _ _ _ (der_30148 v h) (hints_cons _ _ _ (der_30149 v h) (hints_cons _ _ _ (der_30150 v h) (hints_cons _ _ _ (der_30151 v h) (hints_cons _ _ _ (der_30152 v h) (hints_cons _ _ _ (der_30154 v h) (hints_cons _ _ _ (der_30155 v h) (hints_cons _ _ _ (der_30156 v h) (hints_cons _ _ _ (der_30158 v h) (hints_cons _ _ _ (der_30159 v h) (hints_cons _ _ _ (der_30160 v h) (hints_cons _ _ _ (der_30162 v h) (hints_cons _ _ _ (der_30163 v h) (hints_cons _ _ _ (der_30164 v h) (hints_cons _ _ _ (der_30165 v h) (hints_cons _ _ _ (der_30166 v h) (hints_cons _ _ _ (der_30167 v h) (hints_cons _ _ _ (der_30168 v h) (hints_cons _ _ _ (der_30169 v h) (hints_cons _ _ _ (der_30170 v h) (hints_cons _ _ _ (der_30171 v h) (hints_cons _ _ _ (der_30172 v h) (hints_cons _ _ _ (der_30173 v h) (hints_cons _ _ _ (der_30174 v h) (hints_cons _ _ _ (der_30175 v h) (hints_cons _ _ _ (der_30176 v h) (hints_cons _ _ _ (der_30177 v h) (hints_cons _ _ _ (der_30178 v h) (hints_cons _ _ _ (der_30179 v h) (hints_cons _ _ _ (der_30180 v h) (hints_cons _ _ _ (der_30181 v h) (hints_cons _ _ _ (der_30182 v h) (hints_cons _ _ _ (der_30183 v h) (hints_cons _ _ _ (der_30184 v h) (hints_cons _ _ _ (der_30185 v h) (hints_cons _ _ _ (der_30187 v h) (hints_cons _ _ _ (der_30188 v h) (hints_cons _ _ _ (der_30189 v h) (hints_cons _ _ _ (der_30190 v h) (hints_cons _ _ _ (der_30191 v h) (hints_cons _ _ _ (der_30192 v h) (hints_cons _ _ _ (der_30194 v h) (hints_cons _ _ _ (der_30195 v h) (hints_cons _ _ _ (der_30196 v h) (hints_cons _ _ _ (der_30197 v h) (hints_cons _ _ _ (der_30198 v h) (hints_cons _ _ _ (der_30199 v h) (hints_cons _ _ _ (der_30200 v h) (hints_cons _ _ _ (der_30201 v h) (hints_cons _ _ _ (der_30202 v h) (hints_cons _ _ _ (der_30203 v h) (hints_cons _ _ _ (der_30204 v h) (hints_cons _ _ _ (der_30205 v h) (hints_cons _ _ _ (der_30206 v h) (hints_cons _ _ _ (der_30208 v h) (hints_cons _ _ _ (der_30209 v h) (hints_cons _ _ _ (der_30210 v h) (hints_cons _ _ _ (der_30211 v h) (hints_cons _ _ _ (der_30212 v h) (hints_cons _ _ _ (der_30213 v h) (hints_cons _ _ _ (der_30215 v h) (hints_cons _ _ _ (der_30216 v h) (hints_cons _ _ _ (der_30217 v h) (hints_cons _ _ _ (der_30218 v h) (hints_cons _ _ _ (der_30219 v h) (hints_cons _ _ _ (der_30220 v h) (hints_cons _ _ _ (der_30221 v h) (hints_cons _ _ _ (der_30222 v h) (hints_cons _ _ _ (der_30223 v h) (hints_cons _ _ _ (der_30224 v h) (hints_cons _ _ _ (der_30225 v h) (hints_cons _ _ _ (der_30226 v h) (hints_cons _ _ _ (der_30227 v h) (hints_cons _ _ _ (der_30228 v h) (hints_cons _ _ _ (der_30229 v h) (hints_cons _ _ _ (der_30230 v h) (hints_cons _ _ _ (der_30231 v h) (hints_cons _ _ _ (der_30232 v h) (hints_cons _ _ _ (der_30233 v h) (hints_cons _ _ _ (der_30234 v h) (hints_cons _ _ _ (der_30235 v h) (hints_cons _ _ _ (der_30236 v h) (hints_cons _ _ _ (der_30237 v h) (hints_cons _ _ _ (der_30238 v h) (hints_cons _ _ _ (der_30240 v h) (hints_cons _ _ _ (der_30241 v h) (hints_cons _ _ _ (der_30242 v h) (hints_cons _ _ _ (der_30243 v h) (hints_cons _ _ _ (der_30244 v h) (hints_cons _ _ _ (der_30245 v h) (hints_cons _ _ _ (der_30246 v h) (hints_cons _ _ _ (der_30248 v h) (hints_cons _ _ _ (der_30249 v h) (hints_cons _ _ _ (der_30250 v h) (hints_cons _ _ _ (der_30251 v h) (hints_cons _ _ _ (der_30252 v h) (hints_cons _ _ _ (der_30253 v h) (hints_cons _ _ _ (der_30259 v h) (hints_cons _ _ _ (der_30260 v h) (hints_cons _ _ _ (der_30261 v h) (hints_cons _ _ _ (der_30262 v h) (hints_cons _ _ _ (der_30263 v h) (hints_cons _ _ _ (der_30264 v h) (hints_cons _ _ _ (der_30265 v h) (hints_cons _ _ _ (der_30266 v h) (hints_cons _ _ _ (der_30267 v h) (hints_cons _ _ _ (der_30268 v h) (hints_cons _ _ _ (der_30270 v h) (hints_cons _ _ _ (der_30271 v h) (hints_cons _ _ _ (der_30272 v h) (hints_cons _ _ _ (der_30273 v h) (hints_cons _ _ _ (der_30274 v h) (hints_cons _ _ _ (der_30276 v h) (hints_cons _ _ _ (der_30277 v h) (hints_cons _ _ _ (der_30278 v h) (hints_cons _ _ _ (der_30279 v h) (hints_cons _ _ _ (der_30280 v h) (hints_cons _ _ _ (der_30281 v h) (hints_cons _ _ _ (der_30282 v h) (hints_cons _ _ _ (der_30283 v h) (hints_cons _ _ _ (der_30284 v h) (hints_cons _ _ _ (der_30285 v h) (hints_cons _ _ _ (der_30286 v h) (hints_cons _ _ _ (der_30287 v h) (hints_cons _ _ _ (der_30289 v h) (hints_cons _ _ _ (der_30290 v h) (hints_cons _ _ _ (der_30291 v h) (hints_cons _ _ _ (der_30293 v h) (hints_cons _ _ _ (der_30295 v h) (hints_cons _ _ _ (der_30296 v h) (hints_cons _ _ _ (der_30297 v h) (hints_cons _ _ _ (der_30299 v h) (hints_cons _ _ _ (der_30300 v h) (hints_cons _ _ _ (der_30301 v h) (hints_cons _ _ _ (der_30302 v h) (hints_cons _ _ _ (der_30303 v h) (hints_cons _ _ _ (der_30304 v h) (hints_cons _ _ _ (der_30306 v h) (hints_cons _ _ _ (der_30307 v h) (hints_cons _ _ _ (der_30309 v h) (hints_cons _ _ _ (der_30310 v h) (hints_cons _ _ _ (der_30311 v h) (hints_cons _ _ _ (der_30313 v h) (hints_cons _ _ _ (der_30314 v h) (hints_cons _ _ _ (der_30315 v h) (hints_cons _ _ _ (der_30316 v h) (hints_cons _ _ _ (der_30317 v h) (hints_cons _ _ _ (der_30318 v h) (hints_cons _ _ _ (der_30319 v h) (hints_cons _ _ _ (der_30321 v h) (hints_cons _ _ _ (der_30322 v h) (hints_cons _ _ _ (der_30323 v h) (hints_cons _ _ _ (der_30324 v h) (hints_cons _ _ _ (der_30325 v h) (hints_cons _ _ _ (der_30326 v h) (hints_cons _ _ _ (der_30327 v h) (hints_cons _ _ _ (der_30328 v h) (hints_cons _ _ _ (der_30329 v h) (hints_cons _ _ _ (der_30330 v h) (hints_cons _ _ _ (der_30331 v h) (hints_cons _ _ _ (der_30332 v h) (hints_cons _ _ _ (der_30333 v h) (hints_cons _ _ _ (der_30334 v h) (hints_cons _ _ _ (der_30336 v h) (hints_cons _ _ _ (der_30337 v h) (hints_cons _ _ _ (der_30338 v h) (hints_cons _ _ _ (der_30339 v h) (hints_cons _ _ _ (der_30341 v h) (hints_cons _ _ _ (der_30343 v h) (hints_cons _ _ _ (der_30344 v h) (hints_cons _ _ _ (der_30345 v h) (hints_cons _ _ _ (der_30346 v h) (hints_cons _ _ _ (der_30347 v h) (hints_cons _ _ _ (der_30348 v h) (hints_cons _ _ _ (der_30349 v h) (hints_cons _ _ _ (der_30350 v h) (hints_cons _ _ _ (der_30351 v h) (hints_cons _ _ _ (der_30352 v h) (hints_cons _ _ _ (der_30353 v h) (hints_cons _ _ _ (der_30354 v h) (hints_cons _ _ _ (der_30355 v h) (hints_cons _ _ _ (der_30356 v h) (hints_cons _ _ _ (der_30358 v h) (hints_cons _ _ _ (der_30359 v h) (hints_cons _ _ _ (der_30360 v h) (hints_cons _ _ _ (der_30361 v h) (hints_cons _ _ _ (der_30362 v h) (hints_cons _ _ _ (der_30363 v h) (hints_cons _ _ _ (der_30364 v h) (hints_cons _ _ _ (der_30365 v h) (hints_cons _ _ _ (der_30366 v h) (hints_cons _ _ _ (der_30367 v h) (hints_cons _ _ _ (der_30368 v h) (hints_cons _ _ _ (der_30369 v h) (hints_cons _ _ _ (der_30370 v h) (hints_cons _ _ _ (der_30371 v h) (hints_cons _ _ _ (der_30372 v h) (hints_cons _ _ _ (der_30373 v h) (hints_cons _ _ _ (der_30374 v h) (hints_cons _ _ _ (der_30375 v h) (hints_cons _ _ _ (der_30376 v h) (hints_cons _ _ _ (der_30377 v h) (hints_cons _ _ _ (der_30378 v h) (hints_cons _ _ _ (der_30379 v h) (hints_cons _ _ _ (der_30380 v h) (hints_cons _ _ _ (der_30381 v h) (hints_cons _ _ _ (der_30382 v h) (hints_cons _ _ _ (der_30384 v h) (hints_cons _ _ _ (der_30385 v h) (hints_cons _ _ _ (der_30386 v h) (hints_cons _ _ _ (der_30387 v h) (hints_cons _ _ _ (der_30388 v h) (hints_cons _ _ _ (der_30389 v h) (hints_cons _ _ _ (der_30390 v h) (hints_cons _ _ _ (der_30391 v h) (hints_cons _ _ _ (der_30392 v h) (hints_cons _ _ _ (der_30393 v h) (hints_cons _ _ _ (der_30394 v h) (hints_cons _ _ _ (der_30395 v h) (hints_cons _ _ _ (der_30396 v h) (hints_cons _ _ _ (der_30397 v h) (hints_cons _ _ _ (der_30399 v h) (hints_cons _ _ _ (der_30400 v h) (hints_cons _ _ _ (der_30401 v h) (hints_cons _ _ _ (der_30402 v h) (hints_cons _ _ _ (der_30403 v h) (hints_cons _ _ _ (der_30405 v h) (hints_cons _ _ _ (der_30406 v h) (hints_cons _ _ _ (der_30407 v h) (hints_cons _ _ _ (der_30408 v h) (hints_cons _ _ _ (der_30409 v h) (hints_cons _ _ _ (der_30410 v h) (hints_cons _ _ _ (der_30411 v h) (hints_cons _ _ _ (der_30412 v h) (hints_cons _ _ _ (der_30413 v h) (hints_cons _ _ _ (der_30414 v h) (hints_cons _ _ _ (der_30415 v h) (hints_cons _ _ _ (der_30416 v h) (hints_cons _ _ _ (der_30418 v h) (hints_cons _ _ _ (der_30419 v h) (hints_cons _ _ _ (der_30420 v h) (hints_cons _ _ _ (der_30421 v h) (hints_cons _ _ _ (der_30422 v h) (hints_cons _ _ _ (der_30423 v h) (hints_cons _ _ _ (der_30424 v h) (hints_cons _ _ _ (der_30425 v h) (hints_cons _ _ _ (der_30426 v h) (hints_cons _ _ _ (der_30427 v h) (hints_cons _ _ _ (der_30428 v h) (hints_cons _ _ _ (der_30429 v h) (hints_cons _ _ _ (der_30430 v h) (hints_cons _ _ _ (der_30432 v h) (hints_cons _ _ _ (der_30433 v h) (hints_cons _ _ _ (der_30434 v h) (hints_cons _ _ _ (der_30435 v h) (hints_cons _ _ _ (der_30436 v h) (hints_cons _ _ _ (der_30437 v h) (hints_cons _ _ _ (der_30438 v h) (hints_cons _ _ _ (der_30439 v h) (hints_cons _ _ _ (der_30440 v h) (hints_cons _ _ _ (der_30441 v h) (hints_cons _ _ _ (der_30443 v h) (hints_cons _ _ _ (der_30444 v h) (hints_cons _ _ _ (der_30445 v h) (hints_cons _ _ _ (der_30446 v h) (hints_cons _ _ _ (der_30447 v h) (hints_cons _ _ _ (der_30448 v h) (hints_cons _ _ _ (der_30449 v h) (hints_cons _ _ _ (der_30450 v h) (hints_cons _ _ _ (der_30451 v h) (hints_cons _ _ _ (der_30452 v h) (hints_cons _ _ _ (der_30453 v h) (hints_cons _ _ _ (der_30454 v h) (hints_cons _ _ _ (der_30455 v h) (hints_cons _ _ _ (der_30456 v h) (hints_cons _ _ _ (der_30459 v h) (hints_cons _ _ _ (der_30460 v h) (hints_cons _ _ _ (der_30461 v h) (hints_cons _ _ _ (der_30462 v h) (hints_cons _ _ _ (der_30463 v h) (hints_cons _ _ _ (der_30464 v h) (hints_cons _ _ _ (der_30465 v h) (hints_cons _ _ _ (der_30466 v h) (hints_cons _ _ _ (der_30467 v h) (hints_cons _ _ _ (der_30468 v h) (hints_cons _ _ _ (der_30469 v h) (hints_cons _ _ _ (der_30470 v h) (hints_cons _ _ _ (der_30473 v h) (hints_cons _ _ _ (der_30474 v h) (hints_cons _ _ _ (der_30475 v h) (hints_cons _ _ _ (der_30476 v h) (hints_cons _ _ _ (der_30477 v h) (hints_cons _ _ _ (der_30478 v h) (hints_cons _ _ _ (der_30479 v h) (hints_cons _ _ _ (der_30480 v h) (hints_cons _ _ _ (der_30481 v h) (hints_cons _ _ _ (der_30483 v h) (hints_cons _ _ _ (der_30484 v h) (hints_cons _ _ _ (der_30485 v h) (hints_cons _ _ _ (der_30486 v h) (hints_cons _ _ _ (der_30487 v h) (hints_cons _ _ _ (der_30488 v h) (hints_cons _ _ _ (der_30489 v h) (hints_cons _ _ _ (der_30490 v h) (hints_cons _ _ _ (der_30491 v h) (hints_cons _ _ _ (der_30492 v h) (hints_cons _ _ _ (der_30493 v h) (hints_cons _ _ _ (der_30494 v h) (hints_cons _ _ _ (der_30495 v h) (hints_cons _ _ _ (der_30496 v h) (hints_cons _ _ _ (der_30497 v h) (hints_cons _ _ _ (der_30498 v h) (hints_cons _ _ _ (der_30499 v h) (hints_cons _ _ _ (der_30500 v h) (hints_cons _ _ _ (der_30501 v h) (hints_cons _ _ _ (der_30502 v h) (hints_cons _ _ _ (der_30503 v h) (hints_cons _ _ _ (der_30504 v h) (hints_cons _ _ _ (der_30505 v h) (hints_cons _ _ _ (der_30506 v h) (hints_cons _ _ _ (der_30507 v h) (hints_cons _ _ _ (der_30508 v h) (hints_cons _ _ _ (der_30509 v h) (hints_cons _ _ _ (der_30510 v h) (hints_cons _ _ _ (der_30511 v h) (hints_cons _ _ _ (der_30512 v h) (hints_cons _ _ _ (der_30513 v h) (hints_cons _ _ _ (der_30514 v h) (hints_cons _ _ _ (der_30515 v h) (hints_cons _ _ _ (der_30516 v h) (hints_cons _ _ _ (der_30517 v h) (hints_cons _ _ _ (der_30518 v h) (hints_cons _ _ _ (der_30519 v h) (hints_cons _ _ _ (der_30520 v h) (hints_cons _ _ _ (der_30521 v h) (hints_cons _ _ _ (der_30522 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix015 := prefix014 ++ chunk015
theorem prefix_sound015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix015, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound014 v h c hc
  · exact chunk_sound015 v h c hc
end Percolation.NReplay
