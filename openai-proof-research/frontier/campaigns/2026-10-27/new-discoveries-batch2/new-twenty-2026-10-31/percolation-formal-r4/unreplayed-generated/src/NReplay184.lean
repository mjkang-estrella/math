import NReplay183
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_139127 : CNF.NClause := [(11,false),(83,false),(49,false),(85,false),(136,false),(90,false),(52,false),(69,false),(110,false),(98,false),(80,false),(119,false)]
theorem der_139127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139127 :=
  CNF.rup_sound cl_139127 [cl_125539,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125539 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_139129 : CNF.NClause := [(20,false),(10,false),(73,false),(39,false),(146,false),(55,false),(71,false),(70,false),(42,false),(80,false),(69,false),(130,false)]
theorem der_139129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139129 :=
  CNF.rup_sound cl_139129 [cl_125954,cl_107336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125954 v h) (hints_cons _ _ _ (der_107336 v h) (by intro d hd; cases hd)))
def cl_139130 : CNF.NClause := [(89,false),(110,false),(135,false),(148,true),(129,false),(144,true),(145,false),(52,false),(119,false),(97,false),(86,false),(134,false)]
theorem der_139130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139130 :=
  CNF.rup_sound cl_139130 [cl_125910,cl_137961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125910 v h) (hints_cons _ _ _ (der_137961 v h) (by intro d hd; cases hd)))
def cl_139134 : CNF.NClause := [(107,true),(141,false),(84,false),(48,false),(63,false),(138,true),(80,false),(152,true),(24,false),(67,false),(134,false),(127,true)]
theorem der_139134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139134 :=
  CNF.rup_sound cl_139134 [cl_131189,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131189 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_139139 : CNF.NClause := [(34,false),(10,false),(129,false),(74,false),(37,false),(73,false),(136,false),(76,false),(49,false),(75,false),(32,false),(86,false)]
theorem der_139139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139139 :=
  CNF.rup_sound cl_139139 [cl_133353,cl_137961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133353 v h) (hints_cons _ _ _ (der_137961 v h) (by intro d hd; cases hd)))
def cl_139140 : CNF.NClause := [(118,false),(129,true),(32,false),(8,false),(153,true),(43,false),(107,false),(85,false),(130,false),(102,false),(125,false),(138,true)]
theorem der_139140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139140 :=
  CNF.rup_sound cl_139140 [cl_133601,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133601 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_139142 : CNF.NClause := [(60,false),(44,false),(144,false),(148,false),(40,false),(134,false),(74,false),(84,false),(63,false),(130,false),(75,false),(80,false)]
theorem der_139142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139142 :=
  CNF.rup_sound cl_139142 [cl_134469,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134469 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_139143 : CNF.NClause := [(922,true),(917,true),(926,true),(906,true),(74,true),(925,true),(923,true),(903,true),(913,true),(911,true),(900,true),(912,true)]
theorem der_139143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139143 :=
  CNF.rup_sound cl_139143 [cl_134945,cl_75161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134945 v h) (hints_cons _ _ _ (der_75161 v h) (by intro d hd; cases hd)))
def cl_139144 : CNF.NClause := [(142,false),(141,false),(51,false),(85,false),(46,false),(81,false),(137,false),(55,false),(12,false),(77,false),(68,false),(64,false)]
theorem der_139144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139144 :=
  CNF.rup_sound cl_139144 [cl_135170,cl_62596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135170 v h) (hints_cons _ _ _ (der_62596 v h) (by intro d hd; cases hd)))
def cl_139145 : CNF.NClause := [(902,false),(911,true),(913,true),(915,true),(910,true),(921,true),(127,true),(908,true),(925,true),(80,false),(34,true),(70,false)]
theorem der_139145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139145 :=
  CNF.rup_sound cl_139145 [cl_135708,cl_130407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135708 v h) (hints_cons _ _ _ (der_130407 v h) (by intro d hd; cases hd)))
def cl_139148 : CNF.NClause := [(27,false),(147,false),(130,true),(69,false),(126,true),(78,false),(143,true),(76,false),(134,true),(85,false),(140,true),(120,true)]
theorem der_139148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139148 :=
  CNF.rup_sound cl_139148 [cl_137001,cl_132496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137001 v h) (hints_cons _ _ _ (der_132496 v h) (by intro d hd; cases hd)))
def cl_139149 : CNF.NClause := [(923,false),(928,true),(130,false),(48,false),(52,false),(40,false),(44,false),(63,false),(906,true),(50,false),(84,false),(76,false)]
theorem der_139149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139149 :=
  CNF.rup_sound cl_139149 [cl_137294,cl_62077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137294 v h) (hints_cons _ _ _ (der_62077 v h) (by intro d hd; cases hd)))
def cl_139152 : CNF.NClause := [(11,false),(66,false),(83,false),(41,false),(112,false),(98,false),(69,false),(54,false),(75,false),(90,false),(80,false),(120,false),(96,false)]
theorem der_139152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139152 :=
  CNF.rup_sound cl_139152 [cl_80692,cl_115999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80692 v h) (hints_cons _ _ _ (der_115999 v h) (by intro d hd; cases hd)))
def cl_139153 : CNF.NClause := [(114,false),(33,false),(80,false),(63,false),(104,false),(79,false),(99,false),(91,false),(35,false),(76,false),(67,false),(109,false),(24,false)]
theorem der_139153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139153 :=
  CNF.rup_sound cl_139153 [cl_80694,cl_108023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80694 v h) (hints_cons _ _ _ (der_108023 v h) (by intro d hd; cases hd)))
def cl_139154 : CNF.NClause := [(16,false),(89,false),(39,false),(84,false),(96,false),(110,false),(63,false),(50,false),(107,false),(113,false),(75,false),(68,false),(66,false)]
theorem der_139154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139154 :=
  CNF.rup_sound cl_139154 [cl_80697,cl_115973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80697 v h) (hints_cons _ _ _ (der_115973 v h) (by intro d hd; cases hd)))
def cl_139155 : CNF.NClause := [(54,false),(97,false),(84,false),(111,false),(72,false),(88,false),(100,false),(89,false),(78,false),(13,false),(121,false),(71,false),(42,false)]
theorem der_139155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139155 :=
  CNF.rup_sound cl_139155 [cl_107852,cl_137969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107852 v h) (hints_cons _ _ _ (der_137969 v h) (by intro d hd; cases hd)))
def cl_139156 : CNF.NClause := [(33,false),(89,false),(66,false),(67,false),(57,false),(49,false),(71,false),(53,false),(23,false),(76,false),(120,false),(83,false),(1,false)]
theorem der_139156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139156 :=
  CNF.rup_sound cl_139156 [cl_107853,cl_107182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107853 v h) (hints_cons _ _ _ (der_107182 v h) (by intro d hd; cases hd)))
def cl_139157 : CNF.NClause := [(89,false),(111,false),(74,false),(67,false),(55,false),(107,false),(81,false),(83,false),(23,false),(137,false),(94,false),(88,false),(122,false)]
theorem der_139157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139157 :=
  CNF.rup_sound cl_139157 [cl_107856,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107856 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_139158 : CNF.NClause := [(89,false),(38,false),(88,false),(86,false),(134,true),(135,true),(111,false),(137,false),(95,false),(113,false),(104,false),(136,true),(63,false)]
theorem der_139158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139158 :=
  CNF.rup_sound cl_139158 [cl_83515,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83515 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_139160 : CNF.NClause := [(144,false),(113,false),(78,false),(39,false),(121,false),(71,false),(81,false),(107,false),(96,false),(18,false),(15,false),(80,false),(79,false)]
theorem der_139160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139160 :=
  CNF.rup_sound cl_139160 [cl_107859,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107859 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_139161 : CNF.NClause := [(109,false),(100,false),(120,false),(73,false),(84,false),(82,false),(5,false),(86,false),(83,false),(93,false),(134,false),(58,false),(85,false)]
theorem der_139161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139161 :=
  CNF.rup_sound cl_139161 [cl_83976,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83976 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_139162 : CNF.NClause := [(3,false),(109,false),(70,false),(113,false),(86,false),(37,false),(125,false),(75,false),(85,false),(105,false),(80,false),(122,false),(65,false)]
theorem der_139162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139162 :=
  CNF.rup_sound cl_139162 [cl_82110,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82110 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_139164 : CNF.NClause := [(94,false),(113,false),(78,false),(134,false),(40,false),(100,false),(77,false),(80,false),(81,false),(119,false),(75,false),(15,false),(79,false)]
theorem der_139164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139164 :=
  CNF.rup_sound cl_139164 [cl_107862,cl_115970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107862 v h) (hints_cons _ _ _ (der_115970 v h) (by intro d hd; cases hd)))
def cl_139165 : CNF.NClause := [(45,false),(117,false),(15,false),(120,false),(80,false),(71,false),(78,false),(103,false),(144,false),(94,false),(81,false),(79,false),(18,false)]
theorem der_139165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139165 :=
  CNF.rup_sound cl_139165 [cl_107865,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107865 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_139167 : CNF.NClause := [(94,false),(5,false),(119,false),(85,false),(73,false),(100,false),(134,false),(112,false),(84,false),(40,false),(86,false),(82,false),(83,false)]
theorem der_139167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139167 :=
  CNF.rup_sound cl_139167 [cl_88878,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88878 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_139169 : CNF.NClause := [(141,true),(104,false),(131,true),(125,false),(86,false),(52,false),(119,false),(67,false),(148,false),(136,false),(84,false),(69,false),(146,true)]
theorem der_139169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139169 :=
  CNF.rup_sound cl_139169 [cl_88672,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88672 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_139173 : CNF.NClause := [(3,false),(110,false),(75,false),(94,false),(65,false),(125,false),(86,false),(85,false),(120,false),(80,false),(70,false),(45,false),(103,false)]
theorem der_139173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139173 :=
  CNF.rup_sound cl_139173 [cl_93386,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93386 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_139176 : CNF.NClause := [(113,false),(125,false),(151,true),(150,true),(143,true),(152,false),(122,false),(97,false),(139,false),(90,false),(37,false),(131,true),(13,false)]
theorem der_139176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139176 :=
  CNF.rup_sound cl_139176 [cl_107874,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107874 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_139179 : CNF.NClause := [(89,false),(59,false),(121,false),(91,false),(137,false),(76,false),(145,false),(85,false),(152,false),(75,false),(112,false),(138,false),(84,false)]
theorem der_139179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139179 :=
  CNF.rup_sound cl_139179 [cl_97639,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97639 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_139180 : CNF.NClause := [(928,false),(927,true),(913,true),(910,true),(69,true),(915,true),(907,true),(18,true),(911,true),(918,true),(905,true),(906,true),(923,true)]
theorem der_139180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139180 :=
  CNF.rup_sound cl_139180 [cl_106952,cl_114825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106952 v h) (hints_cons _ _ _ (der_114825 v h) (by intro d hd; cases hd)))
def cl_139183 : CNF.NClause := [(110,false),(99,false),(78,false),(148,false),(1,false),(74,false),(84,false),(121,false),(70,false),(6,false),(96,false),(80,false),(39,false)]
theorem der_139183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139183 :=
  CNF.rup_sound cl_139183 [cl_107883,cl_80957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107883 v h) (hints_cons _ _ _ (der_80957 v h) (by intro d hd; cases hd)))
def cl_139189 : CNF.NClause := [(3,false),(110,false),(75,false),(70,false),(71,false),(99,false),(121,false),(113,false),(39,false),(85,false),(86,false),(80,false),(32,false)]
theorem der_139189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139189 :=
  CNF.rup_sound cl_139189 [cl_102838,cl_137955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102838 v h) (hints_cons _ _ _ (der_137955 v h) (by intro d hd; cases hd)))
def cl_139192 : CNF.NClause := [(34,false),(111,false),(85,false),(84,false),(82,false),(72,false),(96,false),(86,false),(83,false),(41,false),(101,false),(118,false),(5,false)]
theorem der_139192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139192 :=
  CNF.rup_sound cl_139192 [cl_108338,cl_115964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108338 v h) (hints_cons _ _ _ (der_115964 v h) (by intro d hd; cases hd)))
def cl_139196 : CNF.NClause := [(121,false),(113,false),(141,false),(77,false),(18,false),(136,false),(96,false),(143,true),(129,true),(127,true),(39,false),(151,true),(73,false)]
theorem der_139196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139196 :=
  CNF.rup_sound cl_139196 [cl_114855,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114855 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_139197 : CNF.NClause := [(144,false),(113,false),(121,false),(138,false),(132,false),(39,false),(110,false),(10,false),(75,false),(74,false),(73,false),(71,false),(96,false)]
theorem der_139197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139197 :=
  CNF.rup_sound cl_139197 [cl_113817,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113817 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_139198 : CNF.NClause := [(50,false),(142,false),(77,false),(75,false),(85,false),(127,false),(70,false),(69,false),(121,false),(148,false),(84,false),(105,false),(125,false)]
theorem der_139198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139198 :=
  CNF.rup_sound cl_139198 [cl_116586,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116586 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_139211 : CNF.NClause := [(109,false),(141,false),(76,false),(53,false),(121,false),(137,false),(136,true),(74,false),(135,true),(138,true),(70,false),(144,false),(117,false)]
theorem der_139211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139211 :=
  CNF.rup_sound cl_139211 [cl_120220,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120220 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_139214 : CNF.NClause := [(130,false),(44,false),(134,false),(119,false),(63,false),(144,false),(80,false),(75,false),(84,false),(74,false),(24,false),(67,false),(96,false)]
theorem der_139214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139214 :=
  CNF.rup_sound cl_139214 [cl_122836,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122836 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_139237 : CNF.NClause := [(108,false),(128,false),(105,false),(116,false),(153,true),(134,false),(150,false),(121,false),(50,false),(140,true),(94,false),(132,true),(74,false)]
theorem der_139237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139237 :=
  CNF.rup_sound cl_139237 [cl_131256,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131256 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_139241 : CNF.NClause := [(153,false),(100,false),(122,false),(77,false),(63,false),(71,false),(13,false),(85,false),(19,false),(49,false),(96,false),(151,true),(150,true)]
theorem der_139241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139241 :=
  CNF.rup_sound cl_139241 [cl_132377,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132377 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_139244 : CNF.NClause := [(152,false),(40,false),(77,false),(151,true),(19,false),(52,false),(63,false),(144,false),(139,false),(68,false),(79,false),(21,false),(150,true)]
theorem der_139244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139244 :=
  CNF.rup_sound cl_139244 [cl_132886,cl_79659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132886 v h) (hints_cons _ _ _ (der_79659 v h) (by intro d hd; cases hd)))
def cl_139248 : CNF.NClause := [(34,false),(132,true),(96,false),(130,true),(129,false),(75,false),(139,false),(131,true),(79,false),(118,false),(101,false),(69,false),(17,false)]
theorem der_139248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139248 :=
  CNF.rup_sound cl_139248 [cl_133199,cl_61659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133199 v h) (hints_cons _ _ _ (der_61659 v h) (by intro d hd; cases hd)))
def cl_139249 : CNF.NClause := [(12,false),(137,false),(60,false),(133,false),(75,false),(17,false),(146,false),(48,false),(5,false),(147,true),(143,false),(69,false),(145,true)]
theorem der_139249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139249 :=
  CNF.rup_sound cl_139249 [cl_133203,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133203 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_139261 : CNF.NClause := [(3,false),(101,false),(142,false),(114,false),(119,false),(55,false),(81,false),(141,false),(80,false),(48,false),(146,true),(131,true),(67,false)]
theorem der_139261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139261 :=
  CNF.rup_sound cl_139261 [cl_136064,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136064 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_139266 : CNF.NClause := [(48,false),(60,false),(52,false),(1,false),(144,false),(135,true),(139,false),(77,false),(136,false),(133,true),(137,false),(151,true),(145,false)]
theorem der_139266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139266 :=
  CNF.rup_sound cl_139266 [cl_136976,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136976 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_139267 : CNF.NClause := [(1057,true),(1074,true),(1064,true),(1062,true),(1083,true),(1073,true),(1065,true),(1058,true),(1055,true),(1070,true),(1077,true),(1059,true),(1081,true)]
theorem der_139267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139267 :=
  CNF.rup_sound cl_139267 [cl_137157,cl_15742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137157 v h) (hints_cons _ _ _ (der_15742 v h) (by intro d hd; cases hd)))
def cl_139268 : CNF.NClause := [(83,true),(909,true),(923,true),(906,true),(907,true),(917,true),(911,true),(913,true),(915,true),(926,true),(914,false),(5,true),(919,true)]
theorem der_139268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139268 :=
  CNF.rup_sound cl_139268 [cl_137327,cl_116082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137327 v h) (hints_cons _ _ _ (der_116082 v h) (by intro d hd; cases hd)))
def cl_139269 : CNF.NClause := [(95,false),(43,false),(151,true),(13,false),(71,false),(65,false),(153,false),(116,false),(122,false),(84,false),(72,false),(22,false),(150,true)]
theorem der_139269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139269 :=
  CNF.rup_sound cl_139269 [cl_137529,cl_76930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137529 v h) (hints_cons _ _ _ (der_76930 v h) (by intro d hd; cases hd)))
def cl_139275 : CNF.NClause := [(26,false),(83,false),(62,false),(146,false),(71,false),(48,false),(46,false),(12,false),(52,false),(41,false),(81,false),(68,false),(60,false),(85,false)]
theorem der_139275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139275 :=
  CNF.rup_sound cl_139275 [cl_80760,cl_115998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80760 v h) (hints_cons _ _ _ (der_115998 v h) (by intro d hd; cases hd)))
def cl_139277 : CNF.NClause := [(54,false),(101,false),(75,false),(91,false),(79,false),(88,false),(71,false),(104,false),(89,false),(152,false),(115,false),(121,false),(59,false),(76,false)]
theorem der_139277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139277 :=
  CNF.rup_sound cl_139277 [cl_87707,cl_87741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87707 v h) (hints_cons _ _ _ (der_87741 v h) (by intro d hd; cases hd)))
def cl_139279 : CNF.NClause := [(89,false),(120,false),(66,false),(137,false),(150,true),(107,false),(58,false),(100,false),(152,false),(67,false),(21,false),(85,false),(59,false),(79,false)]
theorem der_139279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139279 :=
  CNF.rup_sound cl_139279 [cl_95455,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95455 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_139280 : CNF.NClause := [(152,false),(153,true),(104,false),(85,false),(86,false),(128,false),(151,true),(146,false),(79,false),(71,false),(136,false),(35,false),(118,false),(94,false)]
theorem der_139280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139280 :=
  CNF.rup_sound cl_139280 [cl_91165,cl_102901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91165 v h) (hints_cons _ _ _ (der_102901 v h) (by intro d hd; cases hd)))
def cl_139282 : CNF.NClause := [(11,false),(72,false),(94,false),(106,false),(81,false),(130,false),(80,false),(84,false),(62,false),(113,false),(28,false),(40,false),(119,false),(128,false)]
theorem der_139282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139282 :=
  CNF.rup_sound cl_139282 [cl_91484,cl_137989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91484 v h) (hints_cons _ _ _ (der_137989 v h) (by intro d hd; cases hd)))
def cl_139288 : CNF.NClause := [(109,false),(58,false),(133,false),(68,false),(29,false),(107,false),(80,false),(152,true),(151,false),(120,false),(74,false),(116,false),(150,true),(86,false)]
theorem der_139288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139288 :=
  CNF.rup_sound cl_139288 [cl_107910,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107910 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_139293 : CNF.NClause := [(1056,false),(1057,true),(1060,true),(26,true),(1078,true),(11,true),(4,true),(5,true),(1069,true),(1074,true),(17,true),(1067,true),(1083,true),(1055,true)]
theorem der_139293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139293 :=
  CNF.rup_sound cl_139293 [cl_111782,cl_87846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111782 v h) (hints_cons _ _ _ (der_87846 v h) (by intro d hd; cases hd)))
def cl_139297 : CNF.NClause := [(117,false),(14,false),(98,false),(131,false),(144,true),(133,false),(121,false),(125,true),(82,false),(78,false),(53,false),(143,true),(69,false),(150,true)]
theorem der_139297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139297 :=
  CNF.rup_sound cl_139297 [cl_113238,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113238 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_139305 : CNF.NClause := [(39,false),(75,false),(59,false),(71,false),(70,false),(86,false),(66,false),(81,false),(1,false),(93,false),(104,false),(115,false),(54,true),(127,false)]
theorem der_139305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139305 :=
  CNF.rup_sound cl_139305 [cl_122108,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122108 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_139310 : CNF.NClause := [(38,false),(47,false),(111,false),(126,true),(113,false),(152,false),(6,false),(102,false),(108,false),(99,false),(97,false),(131,false),(141,true),(90,false)]
theorem der_139310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139310 :=
  CNF.rup_sound cl_139310 [cl_118200,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118200 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_139314 : CNF.NClause := [(114,false),(129,false),(48,false),(138,true),(107,false),(119,false),(86,false),(130,true),(127,true),(141,false),(90,false),(108,false),(95,false),(83,false)]
theorem der_139314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139314 :=
  CNF.rup_sound cl_139314 [cl_126253,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126253 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_139318 : CNF.NClause := [(39,false),(17,false),(130,false),(125,false),(151,true),(129,true),(75,false),(136,false),(33,false),(64,false),(70,false),(42,false),(32,false),(143,true)]
theorem der_139318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139318 :=
  CNF.rup_sound cl_139318 [cl_126424,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126424 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_139319 : CNF.NClause := [(90,false),(135,false),(146,true),(125,true),(129,true),(143,true),(151,true),(127,true),(148,false),(138,false),(142,true),(140,true),(115,true),(150,true)]
theorem der_139319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139319 :=
  CNF.rup_sound cl_139319 [cl_123742,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123742 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_139322 : CNF.NClause := [(903,true),(904,false),(76,true),(915,true),(917,true),(926,true),(906,true),(914,true),(923,true),(10,true),(919,true),(925,true),(911,true),(913,true)]
theorem der_139322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139322 :=
  CNF.rup_sound cl_139322 [cl_129036,cl_15702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129036 v h) (hints_cons _ _ _ (der_15702 v h) (by intro d hd; cases hd)))
def cl_139326 : CNF.NClause := [(43,false),(143,false),(50,false),(137,false),(133,false),(147,true),(83,false),(73,false),(153,true),(142,false),(129,false),(126,true),(85,false),(42,false)]
theorem der_139326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139326 :=
  CNF.rup_sound cl_139326 [cl_126836,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126836 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_139327 : CNF.NClause := [(99,false),(38,false),(141,false),(110,false),(131,false),(148,false),(120,false),(84,false),(75,false),(150,false),(47,false),(42,false),(90,false),(79,false)]
theorem der_139327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139327 :=
  CNF.rup_sound cl_139327 [cl_125742,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125742 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_139333 : CNF.NClause := [(48,false),(40,false),(70,false),(50,false),(121,false),(76,false),(130,false),(131,true),(83,false),(136,false),(10,false),(143,false),(128,false),(77,false)]
theorem der_139333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139333 :=
  CNF.rup_sound cl_139333 [cl_126521,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126521 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_139334 : CNF.NClause := [(26,false),(118,false),(63,false),(97,false),(53,false),(112,false),(78,false),(102,false),(80,false),(24,false),(76,false),(32,false),(90,false),(84,false)]
theorem der_139334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139334 :=
  CNF.rup_sound cl_139334 [cl_129462,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129462 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_139337 : CNF.NClause := [(142,false),(46,false),(148,false),(152,false),(71,false),(67,false),(51,false),(74,false),(39,false),(80,false),(63,false),(77,false),(85,false),(19,false)]
theorem der_139337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139337 :=
  CNF.rup_sound cl_139337 [cl_132037,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132037 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_139338 : CNF.NClause := [(35,false),(44,false),(78,false),(70,false),(83,false),(69,false),(85,false),(127,false),(20,false),(68,false),(41,false),(129,false),(46,false),(67,false)]
theorem der_139338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139338 :=
  CNF.rup_sound cl_139338 [cl_132269,cl_115761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132269 v h) (hints_cons _ _ _ (der_115761 v h) (by intro d hd; cases hd)))
def cl_139339 : CNF.NClause := [(39,false),(49,false),(37,false),(80,false),(71,false),(78,false),(79,false),(152,false),(15,false),(68,false),(147,true),(146,true),(145,true),(148,false)]
theorem der_139339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139339 :=
  CNF.rup_sound cl_139339 [cl_132493,cl_107181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132493 v h) (hints_cons _ _ _ (der_107181 v h) (by intro d hd; cases hd)))
def cl_139341 : CNF.NClause := [(19,false),(144,false),(70,false),(119,false),(85,false),(40,false),(112,false),(72,false),(132,false),(63,false),(67,false),(134,false),(77,false),(75,false)]
theorem der_139341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139341 :=
  CNF.rup_sound cl_139341 [cl_132615,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132615 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_139352 : CNF.NClause := [(105,false),(136,false),(81,false),(117,false),(146,false),(84,false),(24,false),(119,false),(76,false),(63,false),(80,false),(68,false),(60,false),(93,false)]
theorem der_139352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139352 :=
  CNF.rup_sound cl_139352 [cl_134174,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134174 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_139354 : CNF.NClause := [(123,false),(100,false),(1,false),(102,false),(130,false),(148,false),(143,true),(51,false),(76,false),(80,false),(63,false),(138,true),(133,true),(67,false)]
theorem der_139354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139354 :=
  CNF.rup_sound cl_139354 [cl_134271,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134271 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_139358 : CNF.NClause := [(114,false),(118,false),(139,true),(35,false),(146,true),(99,false),(18,false),(141,false),(104,false),(65,false),(94,false),(84,false),(151,true),(128,false)]
theorem der_139358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139358 :=
  CNF.rup_sound cl_139358 [cl_135314,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135314 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_139362 : CNF.NClause := [(112,false),(110,false),(139,false),(80,false),(46,false),(143,true),(84,false),(123,false),(63,false),(24,false),(130,false),(76,false),(21,false),(140,true)]
theorem der_139362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139362 :=
  CNF.rup_sound cl_139362 [cl_136648,cl_76653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136648 v h) (hints_cons _ _ _ (der_76653 v h) (by intro d hd; cases hd)))
def cl_139363 : CNF.NClause := [(132,true),(111,false),(48,false),(139,false),(153,false),(129,false),(118,false),(105,false),(110,false),(130,false),(33,false),(128,true),(140,true),(64,false)]
theorem der_139363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139363 :=
  CNF.rup_sound cl_139363 [cl_136817,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136817 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_139366 : CNF.NClause := [(10,false),(40,false),(68,false),(112,false),(144,false),(119,false),(94,false),(69,false),(113,false),(75,false),(74,false),(76,false),(72,false),(145,false)]
theorem der_139366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139366 :=
  CNF.rup_sound cl_139366 [cl_137122,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137122 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_139371 : CNF.NClause := [(923,true),(63,true),(925,true),(927,true),(918,true),(907,true),(906,true),(905,true),(904,true),(915,true),(917,true),(919,true),(926,true),(921,true)]
theorem der_139371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139371 :=
  CNF.rup_sound cl_139371 [cl_137844,cl_39956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137844 v h) (hints_cons _ _ _ (der_39956 v h) (by intro d hd; cases hd)))
def cl_139374 : CNF.NClause := [(58,false),(26,false),(144,false),(109,false),(62,false),(79,false),(84,false),(129,false),(86,false),(148,false),(75,false),(71,false),(76,false),(83,false),(120,false)]
theorem der_139374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139374 :=
  CNF.rup_sound cl_139374 [cl_85753,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85753 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_139377 : CNF.NClause := [(107,false),(58,false),(85,false),(72,false),(28,false),(62,false),(73,false),(68,false),(120,false),(12,false),(130,false),(83,false),(84,false),(64,false),(135,false)]
theorem der_139377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139377 :=
  CNF.rup_sound cl_139377 [cl_107922,cl_76603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107922 v h) (hints_cons _ _ _ (der_76603 v h) (by intro d hd; cases hd)))
def cl_139388 : CNF.NClause := [(147,false),(151,false),(85,false),(111,false),(63,false),(50,false),(122,false),(71,false),(19,false),(121,false),(153,true),(77,false),(142,false),(55,false),(107,false)]
theorem der_139388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139388 :=
  CNF.rup_sound cl_139388 [cl_117607,cl_76537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117607 v h) (hints_cons _ _ _ (der_76537 v h) (by intro d hd; cases hd)))
def cl_139391 : CNF.NClause := [(118,false),(141,false),(126,false),(153,true),(147,true),(115,false),(110,false),(138,true),(75,false),(127,true),(130,true),(95,false),(143,true),(152,true),(33,false)]
theorem der_139391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139391 :=
  CNF.rup_sound cl_139391 [cl_122944,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122944 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_139396 : CNF.NClause := [(83,false),(106,false),(95,false),(153,true),(134,true),(26,false),(98,false),(143,true),(126,false),(151,false),(71,false),(121,false),(75,false),(53,false),(117,false)]
theorem der_139396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139396 :=
  CNF.rup_sound cl_139396 [cl_120933,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120933 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_139399 : CNF.NClause := [(35,false),(142,false),(103,false),(5,false),(78,false),(153,true),(4,false),(136,false),(121,false),(141,true),(11,false),(147,true),(112,false),(143,false),(152,false)]
theorem der_139399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139399 :=
  CNF.rup_sound cl_139399 [cl_126840,cl_79710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126840 v h) (hints_cons _ _ _ (der_79710 v h) (by intro d hd; cases hd)))
def cl_139404 : CNF.NClause := [(95,false),(29,false),(151,true),(99,false),(127,true),(136,false),(43,false),(144,false),(112,false),(122,false),(73,false),(70,false),(71,false),(143,true),(103,false)]
theorem der_139404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139404 :=
  CNF.rup_sound cl_139404 [cl_124548,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124548 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_139405 : CNF.NClause := [(11,false),(90,false),(150,false),(116,false),(75,false),(26,false),(142,false),(71,false),(98,false),(72,false),(80,false),(119,false),(52,false),(85,false),(69,false)]
theorem der_139405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139405 :=
  CNF.rup_sound cl_139405 [cl_127329,cl_82801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127329 v h) (hints_cons _ _ _ (der_82801 v h) (by intro d hd; cases hd)))
def cl_139407 : CNF.NClause := [(16,false),(114,false),(129,false),(132,true),(125,false),(108,false),(44,false),(142,false),(135,true),(131,true),(48,false),(133,true),(103,false),(95,false),(68,false)]
theorem der_139407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139407 :=
  CNF.rup_sound cl_139407 [cl_128195,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128195 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_139416 : CNF.NClause := [(100,false),(134,false),(50,false),(70,false),(121,false),(48,false),(128,false),(131,true),(77,false),(136,false),(132,true),(143,false),(133,false),(17,false),(83,false)]
theorem der_139416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139416 :=
  CNF.rup_sound cl_139416 [cl_126522,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126522 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_139425 : CNF.NClause := [(127,true),(153,false),(133,false),(129,true),(17,false),(143,false),(150,false),(121,false),(50,false),(108,false),(72,false),(83,false),(138,false),(132,true),(64,false)]
theorem der_139425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139425 :=
  CNF.rup_sound cl_139425 [cl_131237,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131237 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_139426 : CNF.NClause := [(112,false),(133,true),(126,false),(116,false),(136,false),(127,true),(103,false),(150,false),(95,false),(142,true),(140,true),(70,false),(17,false),(132,true),(125,true)]
theorem der_139426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139426 :=
  CNF.rup_sound cl_139426 [cl_131306,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131306 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_139427 : CNF.NClause := [(50,false),(105,false),(134,true),(65,false),(148,false),(127,false),(121,false),(151,true),(77,false),(85,false),(141,true),(142,false),(69,false),(70,false),(132,true)]
theorem der_139427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139427 :=
  CNF.rup_sound cl_139427 [cl_132433,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132433 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_139434 : CNF.NClause := [(109,false),(13,false),(80,false),(113,false),(37,false),(152,true),(33,false),(125,false),(75,false),(130,false),(65,false),(122,false),(138,true),(144,true),(85,false)]
theorem der_139434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139434 :=
  CNF.rup_sound cl_139434 [cl_133643,cl_138023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133643 v h) (hints_cons _ _ _ (der_138023 v h) (by intro d hd; cases hd)))
def cl_139435 : CNF.NClause := [(77,false),(152,false),(51,false),(18,false),(123,false),(99,false),(74,false),(147,true),(40,false),(119,false),(113,false),(63,false),(143,false),(144,false),(145,true)]
theorem der_139435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139435 :=
  CNF.rup_sound cl_139435 [cl_134561,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134561 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_139440 : CNF.NClause := [(914,true),(920,true),(921,true),(910,true),(901,true),(915,true),(903,true),(922,true),(902,true),(909,true),(906,true),(926,true),(904,true),(907,true),(927,true)]
theorem der_139440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139440 :=
  CNF.rup_sound cl_139440 [cl_135236,cl_15704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135236 v h) (hints_cons _ _ _ (der_15704 v h) (by intro d hd; cases hd)))
def cl_139456 : CNF.NClause := [(54,false),(10,false),(76,false),(75,false),(74,false),(120,false),(13,false),(68,false),(96,false),(98,false),(4,false),(87,false),(63,false),(112,false),(92,false),(28,true)]
theorem der_139456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139456 :=
  CNF.rup_sound cl_139456 [cl_79287,cl_137983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79287 v h) (hints_cons _ _ _ (der_137983 v h) (by intro d hd; cases hd)))
def cl_139457 : CNF.NClause := [(93,false),(60,false),(77,false),(117,false),(99,false),(75,false),(78,false),(15,false),(119,false),(80,false),(10,false),(73,false),(72,false),(79,false),(76,false),(81,false)]
theorem der_139457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139457 :=
  CNF.rup_sound cl_139457 [cl_59191,cl_108024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59191 v h) (hints_cons _ _ _ (der_108024 v h) (by intro d hd; cases hd)))
def cl_139458 : CNF.NClause := [(106,false),(5,false),(62,false),(105,false),(103,false),(107,false),(82,false),(90,false),(73,false),(85,false),(83,false),(81,false),(86,false),(70,false),(41,false),(28,false)]
theorem der_139458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139458 :=
  CNF.rup_sound cl_139458 [cl_62263,cl_115999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62263 v h) (hints_cons _ _ _ (der_115999 v h) (by intro d hd; cases hd)))
def cl_139461 : CNF.NClause := [(89,false),(97,false),(64,false),(78,false),(102,false),(117,false),(32,false),(141,true),(91,false),(84,false),(118,false),(134,true),(125,false),(85,false),(132,true),(136,false)]
theorem der_139461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139461 :=
  CNF.rup_sound cl_139461 [cl_95227,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95227 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_139468 : CNF.NClause := [(113,false),(65,false),(3,false),(137,true),(144,true),(100,false),(85,false),(148,false),(143,true),(75,false),(70,false),(131,true),(80,false),(150,false),(40,false),(119,false)]
theorem der_139468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139468 :=
  CNF.rup_sound cl_139468 [cl_120507,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120507 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_139508 : CNF.NClause := [(141,true),(40,false),(138,true),(132,true),(129,true),(98,false),(90,false),(52,false),(130,false),(63,false),(152,false),(125,false),(131,true),(126,false),(128,true),(85,false)]
theorem der_139508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139508 :=
  CNF.rup_sound cl_139508 [cl_137443,cl_64135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137443 v h) (hints_cons _ _ _ (der_64135 v h) (by intro d hd; cases hd)))
def cl_139514 : CNF.NClause := [(89,false),(34,true),(63,false),(39,false),(24,false),(84,false),(41,true),(121,false),(91,false),(99,false),(81,false),(113,false),(80,false),(83,false),(74,false),(110,false),(23,false)]
theorem der_139514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139514 :=
  CNF.rup_sound cl_139514 [cl_107080,cl_113157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107080 v h) (hints_cons _ _ _ (der_113157 v h) (by intro d hd; cases hd)))
def cl_139516 : CNF.NClause := [(89,false),(41,true),(147,false),(133,true),(84,false),(128,false),(12,false),(121,false),(34,true),(39,false),(113,false),(143,true),(76,false),(126,false),(63,false),(138,true),(80,false)]
theorem der_139516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139516 :=
  CNF.rup_sound cl_139516 [cl_107956,cl_81199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107956 v h) (hints_cons _ _ _ (der_81199 v h) (by intro d hd; cases hd)))
def cl_139539 : CNF.NClause := [(104,false),(9,false),(152,false),(59,false),(126,false),(115,false),(151,true),(76,false),(112,false),(67,false),(101,false),(71,false),(75,false),(80,false),(121,false),(24,false),(83,false)]
theorem der_139539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139539 :=
  CNF.rup_sound cl_139539 [cl_129912,cl_54538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129912 v h) (hints_cons _ _ _ (der_54538 v h) (by intro d hd; cases hd)))
def cl_139559 : CNF.NClause := [(109,false),(97,false),(139,false),(113,false),(96,false),(153,false),(37,false),(130,false),(71,false),(104,false),(84,false),(68,false),(49,false),(8,false),(127,true),(85,false),(21,false)]
theorem der_139559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139559 :=
  CNF.rup_sound cl_139559 [cl_137910,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137910 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_139560 : CNF.NClause := [(89,false),(101,false),(79,false),(62,false),(59,false),(121,false),(112,false),(152,false),(104,false),(86,false),(63,false),(150,true),(137,false),(70,false),(71,false),(88,false),(14,false),(78,false)]
theorem der_139560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139560 :=
  CNF.rup_sound cl_139560 [cl_81449,cl_61980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_81449 v h) (hints_cons _ _ _ (der_61980 v h) (by intro d hd; cases hd)))
def cl_139561 : CNF.NClause := [(3,false),(40,false),(119,false),(79,false),(65,false),(80,false),(113,false),(84,false),(74,false),(146,true),(141,true),(126,false),(85,false),(142,false),(81,false),(131,true),(94,false),(70,false)]
theorem der_139561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139561 :=
  CNF.rup_sound cl_139561 [cl_105626,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105626 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_139579 : CNF.NClause := [(114,false),(152,true),(80,false),(138,true),(134,false),(90,false),(133,true),(127,true),(67,false),(48,false),(150,true),(141,false),(24,false),(63,false),(84,false),(140,true),(119,false),(108,false)]
theorem der_139579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139579 :=
  CNF.rup_sound cl_139579 [cl_131190,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131190 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_139586 : CNF.NClause := [(3,false),(153,false),(43,false),(131,true),(148,false),(65,false),(152,false),(70,false),(80,false),(76,false),(144,true),(137,false),(53,false),(85,false),(78,false),(90,false),(59,false),(150,true)]
theorem der_139586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139586 :=
  CNF.rup_sound cl_139586 [cl_133095,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133095 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_139619 : CNF.NClause := [(28,false),(84,false),(148,false),(53,false),(137,true),(29,false),(80,false),(127,true),(86,false),(76,false),(40,false),(74,false),(73,false),(142,false),(81,false),(147,true),(88,false),(70,false),(63,false)]
theorem der_139619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139619 :=
  CNF.rup_sound cl_139619 [cl_133059,cl_49759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133059 v h) (hints_cons _ _ _ (der_49759 v h) (by intro d hd; cases hd)))
def cl_139686 : CNF.NClause := [(38,false),(54,false),(53,true),(24,true),(126,false),(76,false),(41,true),(100,false),(20,false),(1,true),(34,true),(70,false),(63,false),(8,true),(106,false),(57,true),(140,false),(77,false),(138,false),(72,false),(83,false),(73,false)]
theorem der_139686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139686 :=
  CNF.rup_sound cl_139686 [cl_130445,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130445 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_139704 : CNF.NClause := [(51,false),(135,false),(153,true),(142,true),(130,false),(125,false),(65,false),(143,true),(134,false),(8,true),(139,false),(36,false),(86,false),(147,true),(140,false),(137,true),(73,false),(67,false),(79,false),(85,false),(21,false),(70,false),(64,true)]
theorem der_139704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139704 :=
  CNF.rup_sound cl_139704 [cl_132868,cl_105702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132868 v h) (hints_cons _ _ _ (der_105702 v h) (by intro d hd; cases hd)))
def cl_139751 : CNF.NClause := [(106,false),(1055,true),(129,false),(76,false),(79,false),(1068,true),(39,true),(1056,true),(95,false),(65,false),(52,true),(1060,true),(88,false),(1066,true),(1081,true),(82,false),(109,false),(1080,true),(90,false),(1072,true),(53,false),(121,false),(1070,true),(70,false),(1061,true),(1058,true),(67,false),(71,false),(73,false)]
theorem der_139751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139751 :=
  CNF.rup_sound cl_139751 [cl_133447,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133447 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_139768 : CNF.NClause := [(74,true),(54,false)]
theorem der_139768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139768 :=
  CNF.rup_sound cl_139768 [cl_137986,cl_115725,cl_49772,cl_15868,cl_76630,cl_15894,cl_45005,cl_15876,cl_76628,cl_15885,cl_42451,cl_15872,cl_12691,cl_49829,cl_15884,cl_49765,cl_15879,cl_49884,cl_15874,cl_49831,cl_15869,cl_15670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137986 v h) (hints_cons _ _ _ (der_115725 v h) (hints_cons _ _ _ (der_49772 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_76630 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_45005 v h) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_76628 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_42451 v h) (hints_cons _ _ _ (der_15872 v h) (hints_cons _ _ _ (inp_12691 v h) (hints_cons _ _ _ (der_49829 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_49765 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_49884 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_49831 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_15670 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139769 : CNF.NClause := [(65,true),(54,false)]
theorem der_139769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139769 :=
  CNF.rup_sound cl_139769 [cl_139768,cl_137982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139768 v h) (hints_cons _ _ _ (der_137982 v h) (by intro d hd; cases hd)))
def cl_139770 : CNF.NClause := [(69,true),(40,false)]
theorem der_139770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139770 :=
  CNF.rup_sound cl_139770 [cl_137989,cl_105772,cl_79476,cl_79726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137989 v h) (hints_cons _ _ _ (der_105772 v h) (hints_cons _ _ _ (der_79476 v h) (hints_cons _ _ _ (der_79726 v h) (by intro d hd; cases hd)))))
def cl_139771 : CNF.NClause := [(73,true),(35,false)]
theorem der_139771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139771 :=
  CNF.rup_sound cl_139771 [cl_137998,cl_137999,cl_80048,cl_107257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137998 v h) (hints_cons _ _ _ (der_137999 v h) (hints_cons _ _ _ (der_80048 v h) (hints_cons _ _ _ (der_107257 v h) (by intro d hd; cases hd)))))
def cl_139772 : CNF.NClause := [(63,true),(35,false)]
theorem der_139772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139772 :=
  CNF.rup_sound cl_139772 [cl_107256,cl_139771,cl_79480,cl_79577,cl_49833,cl_15890,cl_41429,cl_15885,cl_42528,cl_15875,cl_42527,cl_15880,cl_15668,cl_79713,cl_15891,cl_79710,cl_15871,cl_79666,cl_15889,cl_105731,cl_15883,cl_62292,cl_15877,cl_12749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107256 v h) (hints_cons _ _ _ (der_139771 v h) (hints_cons _ _ _ (der_79480 v h) (hints_cons _ _ _ (der_79577 v h) (hints_cons _ _ _ (der_49833 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_41429 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_42528 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_42527 v h) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_15668 v h) (hints_cons _ _ _ (der_79713 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_79710 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_79666 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_105731 v h) (hints_cons _ _ _ (der_15883 v h) (hints_cons _ _ _ (der_62292 v h) (hints_cons _ _ _ (der_15877 v h) (hints_cons _ _ _ (inp_12749 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_139773 : CNF.NClause := [(84,true),(36,false)]
theorem der_139773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139773 :=
  CNF.rup_sound cl_139773 [cl_107247,cl_107185,cl_76548,cl_13748,cl_49830,cl_14183,cl_76645,cl_14179,cl_65888,cl_14171,cl_37830,cl_14158,cl_10521,cl_105730,cl_14181,cl_54211,cl_14178,cl_105755,cl_14172,cl_82809,cl_14167,cl_79710,cl_14160,cl_10516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107247 v h) (hints_cons _ _ _ (der_107185 v h) (hints_cons _ _ _ (der_76548 v h) (hints_cons _ _ _ (inp_13748 v h) (hints_cons _ _ _ (der_49830 v h) (hints_cons _ _ _ (inp_14183 v h) (hints_cons _ _ _ (der_76645 v h) (hints_cons _ _ _ (inp_14179 v h) (hints_cons _ _ _ (der_65888 v h) (hints_cons _ _ _ (inp_14171 v h) (hints_cons _ _ _ (der_37830 v h) (hints_cons _ _ _ (inp_14158 v h) (hints_cons _ _ _ (inp_10521 v h) (hints_cons _ _ _ (der_105730 v h) (hints_cons _ _ _ (inp_14181 v h) (hints_cons _ _ _ (der_54211 v h) (hints_cons _ _ _ (inp_14178 v h) (hints_cons _ _ _ (der_105755 v h) (hints_cons _ _ _ (inp_14172 v h) (hints_cons _ _ _ (der_82809 v h) (hints_cons _ _ _ (inp_14167 v h) (hints_cons _ _ _ (der_79710 v h) (hints_cons _ _ _ (inp_14160 v h) (hints_cons _ _ _ (inp_10516 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_139774 : CNF.NClause := [(73,true),(52,false)]
theorem der_139774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139774 :=
  CNF.rup_sound cl_139774 [cl_138001,cl_79554,cl_76632,cl_13753,cl_76901,cl_14333,cl_49967,cl_14310,cl_79673,cl_14316,cl_50010,cl_14313,cl_11384,cl_76964,cl_14309,cl_79659,cl_14324,cl_79639,cl_14318,cl_60483,cl_14311,cl_76654,cl_14332,cl_11455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138001 v h) (hints_cons _ _ _ (der_79554 v h) (hints_cons _ _ _ (der_76632 v h) (hints_cons _ _ _ (inp_13753 v h) (hints_cons _ _ _ (der_76901 v h) (hints_cons _ _ _ (inp_14333 v h) (hints_cons _ _ _ (der_49967 v h) (hints_cons _ _ _ (inp_14310 v h) (hints_cons _ _ _ (der_79673 v h) (hints_cons _ _ _ (inp_14316 v h) (hints_cons _ _ _ (der_50010 v h) (hints_cons _ _ _ (inp_14313 v h) (hints_cons _ _ _ (inp_11384 v h) (hints_cons _ _ _ (der_76964 v h) (hints_cons _ _ _ (inp_14309 v h) (hints_cons _ _ _ (der_79659 v h) (hints_cons _ _ _ (inp_14324 v h) (hints_cons _ _ _ (der_79639 v h) (hints_cons _ _ _ (inp_14318 v h) (hints_cons _ _ _ (der_60483 v h) (hints_cons _ _ _ (inp_14311 v h) (hints_cons _ _ _ (der_76654 v h) (hints_cons _ _ _ (inp_14332 v h) (hints_cons _ _ _ (inp_11455 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_139775 : CNF.NClause := [(67,true),(52,false)]
theorem der_139775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139775 :=
  CNF.rup_sound cl_139775 [cl_107262,cl_79554,cl_76653,cl_15930,cl_49786,cl_15929,cl_76589,cl_15928,cl_49834,cl_15926,cl_15738,cl_76654,cl_15932,cl_60483,cl_15911,cl_79659,cl_15925,cl_76964,cl_15909,cl_79639,cl_15918,cl_13687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107262 v h) (hints_cons _ _ _ (der_79554 v h) (hints_cons _ _ _ (der_76653 v h) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_49786 v h) (hints_cons _ _ _ (der_15929 v h) (hints_cons _ _ _ (der_76589 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (der_49834 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (der_15738 v h) (hints_cons _ _ _ (der_76654 v h) (hints_cons _ _ _ (der_15932 v h) (hints_cons _ _ _ (der_60483 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_79659 v h) (hints_cons _ _ _ (der_15925 v h) (hints_cons _ _ _ (der_76964 v h) (hints_cons _ _ _ (der_15909 v h) (hints_cons _ _ _ (der_79639 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (inp_13687 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139776 : CNF.NClause := [(90,true),(53,false)]
theorem der_139776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139776 :=
  CNF.rup_sound cl_139776 [cl_107236,cl_138016,cl_107266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107236 v h) (hints_cons _ _ _ (der_138016 v h) (hints_cons _ _ _ (der_107266 v h) (by intro d hd; cases hd))))
def cl_139777 : CNF.NClause := [(85,true),(50,false)]
theorem der_139777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139777 :=
  CNF.rup_sound cl_139777 [cl_131684,cl_79547,cl_76614,cl_15793,cl_76612,cl_15774,cl_76892,cl_15778,cl_49887,cl_15771,cl_56362,cl_15769,cl_79659,cl_15787,cl_54563,cl_15792,cl_8108,cl_49803,cl_15788,cl_76544,cl_15777,cl_15664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131684 v h) (hints_cons _ _ _ (der_79547 v h) (hints_cons _ _ _ (der_76614 v h) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_76612 v h) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_76892 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_49887 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_56362 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_79659 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_54563 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (inp_8108 v h) (hints_cons _ _ _ (der_49803 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_76544 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_15664 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139778 : CNF.NClause := [(81,true),(54,false)]
theorem der_139778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139778 :=
  CNF.rup_sound cl_139778 [cl_139768,cl_139769,cl_79798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139768 v h) (hints_cons _ _ _ (der_139769 v h) (hints_cons _ _ _ (der_79798 v h) (by intro d hd; cases hd))))
def cl_139779 : CNF.NClause := [(83,true),(54,false)]
theorem der_139779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139779 :=
  CNF.rup_sound cl_139779 [cl_139769,cl_139778,cl_79804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139769 v h) (hints_cons _ _ _ (der_139778 v h) (hints_cons _ _ _ (der_79804 v h) (by intro d hd; cases hd))))
def cl_139780 : CNF.NClause := [(89,true),(54,false)]
theorem der_139780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139780 :=
  CNF.rup_sound cl_139780 [cl_139768,cl_139769,cl_79802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139768 v h) (hints_cons _ _ _ (der_139769 v h) (hints_cons _ _ _ (der_79802 v h) (by intro d hd; cases hd))))
def cl_139781 : CNF.NClause := [(78,false),(70,true),(37,false)]
theorem der_139781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139781 :=
  CNF.rup_sound cl_139781 [cl_107314,cl_77046,cl_79562,cl_37342,cl_15778,cl_49760,cl_15791,cl_49809,cl_15780,cl_49810,cl_15786,cl_49827,cl_15769,cl_62028,cl_15793,cl_76616,cl_15783,cl_8020,cl_49793,cl_15790,cl_49794,cl_15784,cl_15665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107314 v h) (hints_cons _ _ _ (der_77046 v h) (hints_cons _ _ _ (der_79562 v h) (hints_cons _ _ _ (der_37342 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_49760 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_49809 v h) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_49810 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_49827 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_62028 v h) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_76616 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (inp_8020 v h) (hints_cons _ _ _ (der_49793 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_49794 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15665 v h) (by intro d hd; cases hd))))))))))))))))))))))))
def cl_139782 : CNF.NClause := [(82,true),(6,false),(37,false)]
theorem der_139782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139782 :=
  CNF.rup_sound cl_139782 [cl_105819,cl_37342,cl_15918,cl_49794,cl_15924,cl_49780,cl_15913,cl_29851,cl_15914,cl_49781,cl_15911,cl_42432,cl_15915,cl_15741,cl_49760,cl_15931,cl_49793,cl_15930,cl_15762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105819 v h) (hints_cons _ _ _ (der_37342 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_49794 v h) (hints_cons _ _ _ (der_15924 v h) (hints_cons _ _ _ (der_49780 v h) (hints_cons _ _ _ (der_15913 v h) (hints_cons _ _ _ (der_29851 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_49781 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_42432 v h) (hints_cons _ _ _ (der_15915 v h) (hints_cons _ _ _ (der_15741 v h) (hints_cons _ _ _ (der_49760 v h) (hints_cons _ _ _ (der_15931 v h) (hints_cons _ _ _ (der_49793 v h) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_15762 v h) (by intro d hd; cases hd))))))))))))))))))))
def cl_139783 : CNF.NClause := [(70,false),(66,true),(37,false)]
theorem der_139783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139783 :=
  CNF.rup_sound cl_139783 [cl_50549,cl_139782,cl_138041,cl_107315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50549 v h) (hints_cons _ _ _ (der_139782 v h) (hints_cons _ _ _ (der_138041 v h) (hints_cons _ _ _ (der_107315 v h) (by intro d hd; cases hd)))))
def cl_139784 : CNF.NClause := [(91,true),(82,false),(37,false)]
theorem der_139784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139784 :=
  CNF.rup_sound cl_139784 [cl_138041,cl_79562,cl_37342,cl_15778,cl_49760,cl_15791,cl_49793,cl_15790,cl_139781,cl_79665,cl_15779,cl_79668,cl_15781,cl_76796,cl_15770,cl_79669,cl_15788,cl_76647,cl_15792,cl_8068,cl_49794,cl_15784,cl_15665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138041 v h) (hints_cons _ _ _ (der_79562 v h) (hints_cons _ _ _ (der_37342 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_49760 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_49793 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_139781 v h) (hints_cons _ _ _ (der_79665 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_79668 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_76796 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_79669 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_76647 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (inp_8068 v h) (hints_cons _ _ _ (der_49794 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15665 v h) (by intro d hd; cases hd))))))))))))))))))))))))
def cl_139785 : CNF.NClause := [(81,false),(63,true),(40,false)]
theorem der_139785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139785 :=
  CNF.rup_sound cl_139785 [cl_79810,cl_139770,cl_79532,cl_49838,cl_15787,cl_35284,cl_15779,cl_54538,cl_15790,cl_42528,cl_15770,cl_53715,cl_15785,cl_53720,cl_15780,cl_15624,cl_49837,cl_15794,cl_49835,cl_15783,cl_15662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79810 v h) (hints_cons _ _ _ (der_139770 v h) (hints_cons _ _ _ (der_79532 v h) (hints_cons _ _ _ (der_49838 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_35284 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_54538 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_42528 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_53715 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_53720 v h) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_15624 v h) (hints_cons _ _ _ (der_49837 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_49835 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15662 v h) (by intro d hd; cases hd))))))))))))))))))))))
def cl_139786 : CNF.NClause := [(81,false),(88,true),(40,false)]
theorem der_139786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139786 :=
  CNF.rup_sound cl_139786 [cl_138044,cl_139770,cl_79532,cl_79662,cl_15782,cl_49838,cl_15787,cl_35284,cl_15779,cl_49835,cl_15783,cl_49837,cl_15794,cl_15662,cl_44586,cl_15769,cl_49815,cl_15788,cl_79686,cl_15791,cl_49811,cl_15776,cl_8050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138044 v h) (hints_cons _ _ _ (der_139770 v h) (hints_cons _ _ _ (der_79532 v h) (hints_cons _ _ _ (der_79662 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_49838 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_35284 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_49835 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_49837 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15662 v h) (hints_cons _ _ _ (der_44586 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_49815 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_79686 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_49811 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (inp_8050 v h) (by intro d hd; cases hd))))))))))))))))))))))))
def cl_139787 : CNF.NClause := [(90,false),(81,true),(59,false)]
theorem der_139787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139787 :=
  CNF.rup_sound cl_139787 [cl_79561,cl_80000,cl_79999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79561 v h) (hints_cons _ _ _ (der_80000 v h) (hints_cons _ _ _ (der_79999 v h) (by intro d hd; cases hd))))
def cl_139788 : CNF.NClause := [(90,false),(73,true),(59,false)]
theorem der_139788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139788 :=
  CNF.rup_sound cl_139788 [cl_139787,cl_105978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139787 v h) (hints_cons _ _ _ (der_105978 v h) (by intro d hd; cases hd)))
def cl_139789 : CNF.NClause := [(81,false),(70,true),(59,false)]
theorem der_139789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139789 :=
  CNF.rup_sound cl_139789 [cl_80008,cl_79482,cl_105980,cl_79560,cl_79685,cl_15780,cl_62028,cl_15772,cl_49686,cl_15769,cl_76841,cl_15783,cl_76870,cl_15786,cl_8016,cl_49920,cl_15774,cl_76614,cl_15785,cl_49805,cl_15788,cl_42458,cl_15777,cl_15664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80008 v h) (hints_cons _ _ _ (der_79482 v h) (hints_cons _ _ _ (der_105980 v h) (hints_cons _ _ _ (der_79560 v h) (hints_cons _ _ _ (der_79685 v h) (hints_cons _ _ _ (der_15780 v h) (hints_cons _ _ _ (der_62028 v h) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_49686 v h) (hints_cons _ _ _ (der_15769 v h) (hints_cons _ _ _ (der_76841 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_76870 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (inp_8016 v h) (hints_cons _ _ _ (der_49920 v h) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_76614 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_49805 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_42458 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_15664 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_139790 : CNF.NClause := [(84,true),(28,false),(59,false)]
theorem der_139790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139790 :=
  CNF.rup_sound cl_139790 [cl_105987,cl_43180,cl_15779,cl_49830,cl_15771,cl_76582,cl_15768,cl_43934,cl_15790,cl_42738,cl_15782,cl_8100,cl_139788,cl_49920,cl_15774,cl_76614,cl_15785,cl_49805,cl_15788,cl_42458,cl_15777,cl_15664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105987 v h) (hints_cons _ _ _ (der_43180 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_49830 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_76582 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_43934 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_42738 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (inp_8100 v h) (hints_cons _ _ _ (der_139788 v h) (hints_cons _ _ _ (der_49920 v h) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_76614 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_49805 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_42458 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_15664 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139791 : CNF.NClause := [(81,false),(90,true),(59,false)]
theorem der_139791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139791 :=
  CNF.rup_sound cl_139791 [cl_139789,cl_105985,cl_105980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139789 v h) (hints_cons _ _ _ (der_105985 v h) (hints_cons _ _ _ (der_105980 v h) (by intro d hd; cases hd))))
def cl_139792 : CNF.NClause := [(62,true),(70,false),(59,false)]
theorem der_139792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139792 :=
  CNF.rup_sound cl_139792 [cl_105985,cl_79561,cl_76603,cl_15778,cl_61656,cl_15781,cl_76610,cl_15767,cl_76961,cl_15789,cl_76606,cl_15775,cl_8082,cl_139787,cl_49920,cl_15774,cl_76614,cl_15785,cl_49805,cl_15788,cl_42458,cl_15777,cl_15664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105985 v h) (hints_cons _ _ _ (der_79561 v h) (hints_cons _ _ _ (der_76603 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_61656 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_76610 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_76961 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_76606 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (inp_8082 v h) (hints_cons _ _ _ (der_139787 v h) (hints_cons _ _ _ (der_49920 v h) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_76614 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_49805 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_42458 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_15664 v h) (by intro d hd; cases hd))))))))))))))))))))))))
def cl_139793 : CNF.NClause := [(68,false),(69,true),(51,false)]
theorem der_139793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139793 :=
  CNF.rup_sound cl_139793 [cl_106020,cl_80061,cl_49778,cl_15876,cl_79633,cl_15875,cl_47172,cl_15892,cl_76649,cl_15868,cl_79634,cl_15877,cl_56878,cl_15884,cl_12661,cl_29840,cl_15881,cl_29838,cl_15871,cl_15716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106020 v h) (hints_cons _ _ _ (der_80061 v h) (hints_cons _ _ _ (der_49778 v h) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_79633 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_47172 v h) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_76649 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_79634 v h) (hints_cons _ _ _ (der_15877 v h) (hints_cons _ _ _ (der_56878 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (inp_12661 v h) (hints_cons _ _ _ (der_29840 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_29838 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_15716 v h) (by intro d hd; cases hd)))))))))))))))))))))
def cl_139794 : CNF.NClause := [(68,false),(71,true),(51,false)]
theorem der_139794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139794 :=
  CNF.rup_sound cl_139794 [cl_80057,cl_106013,cl_80061,cl_42754,cl_15791,cl_76594,cl_15773,cl_49828,cl_15785,cl_42582,cl_15767,cl_76597,cl_15779,cl_29838,cl_15771,cl_49778,cl_15776,cl_29840,cl_15781,cl_15666,cl_8023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80057 v h) (hints_cons _ _ _ (der_106013 v h) (hints_cons _ _ _ (der_80061 v h) (hints_cons _ _ _ (der_42754 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_76594 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_49828 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_42582 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_76597 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_29838 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_49778 v h) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (der_29840 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_15666 v h) (hints_cons _ _ _ (inp_8023 v h) (by intro d hd; cases hd))))))))))))))))))))))
def cl_139795 : CNF.NClause := [(70,false),(67,true),(51,false)]
theorem der_139795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139795 :=
  CNF.rup_sound cl_139795 [cl_106024,cl_79565,cl_76594,cl_15913,cl_42582,cl_15907,cl_42754,cl_15931,cl_49828,cl_15925,cl_76597,cl_15919,cl_13603,cl_49834,cl_15927,cl_76550,cl_15928,cl_43960,cl_15929,cl_76549,cl_15930,cl_15738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106024 v h) (hints_cons _ _ _ (der_79565 v h) (hints_cons _ _ _ (der_76594 v h) (hints_cons _ _ _ (der_15913 v h) (hints_cons _ _ _ (der_42582 v h) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_42754 v h) (hints_cons _ _ _ (der_15931 v h) (hints_cons _ _ _ (der_49828 v h) (hints_cons _ _ _ (der_15925 v h) (hints_cons _ _ _ (der_76597 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (inp_13603 v h) (hints_cons _ _ _ (der_49834 v h) (hints_cons _ _ _ (der_15927 v h) (hints_cons _ _ _ (der_76550 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (der_43960 v h) (hints_cons _ _ _ (der_15929 v h) (hints_cons _ _ _ (der_76549 v h) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_15738 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139796 : CNF.NClause := [(87,true),(83,false),(35,false)]
theorem der_139796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139796 :=
  CNF.rup_sound cl_139796 [cl_139771,cl_79480,cl_106008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139771 v h) (hints_cons _ _ _ (der_79480 v h) (hints_cons _ _ _ (der_106008 v h) (by intro d hd; cases hd))))
def cl_139797 : CNF.NClause := [(69,false),(66,true),(42,false)]
theorem der_139797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139797 :=
  CNF.rup_sound cl_139797 [cl_107338,cl_105925,cl_80339,cl_36174,cl_15872,cl_29813,cl_15867,cl_107336,cl_79646,cl_15881,cl_76615,cl_15873,cl_42483,cl_15869,cl_79649,cl_15890,cl_62000,cl_15894,cl_12729,cl_49787,cl_15887,cl_29847,cl_15882,cl_15671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107338 v h) (hints_cons _ _ _ (der_105925 v h) (hints_cons _ _ _ (der_80339 v h) (hints_cons _ _ _ (der_36174 v h) (hints_cons _ _ _ (der_15872 v h) (hints_cons _ _ _ (der_29813 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_107336 v h) (hints_cons _ _ _ (der_79646 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_76615 v h) (hints_cons _ _ _ (der_15873 v h) (hints_cons _ _ _ (der_42483 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_79649 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_62000 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (inp_12729 v h) (hints_cons _ _ _ (der_49787 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_29847 v h) (hints_cons _ _ _ (der_15882 v h) (hints_cons _ _ _ (der_15671 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_139798 : CNF.NClause := [(85,true),(83,true),(36,false)]
theorem der_139798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139798 :=
  CNF.rup_sound cl_139798 [cl_139773,cl_79773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139773 v h) (hints_cons _ _ _ (der_79773 v h) (by intro d hd; cases hd)))
def cl_139799 : CNF.NClause := [(86,false),(82,true),(36,false)]
theorem der_139799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139799 :=
  CNF.rup_sound cl_139799 [cl_105827,cl_79515,cl_76573,cl_15915,cl_76575,cl_15913,cl_49781,cl_15912,cl_76574,cl_15914,cl_15741,cl_37437,cl_15916,cl_29839,cl_15921,cl_29838,cl_15926,cl_15766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105827 v h) (hints_cons _ _ _ (der_79515 v h) (hints_cons _ _ _ (der_76573 v h) (hints_cons _ _ _ (der_15915 v h) (hints_cons _ _ _ (der_76575 v h) (hints_cons _ _ _ (der_15913 v h) (hints_cons _ _ _ (der_49781 v h) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_76574 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_15741 v h) (hints_cons _ _ _ (der_37437 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_29839 v h) (hints_cons _ _ _ (der_15921 v h) (hints_cons _ _ _ (der_29838 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (der_15766 v h) (by intro d hd; cases hd)))))))))))))))))))
def cl_139800 : CNF.NClause := [(92,true),(86,false),(36,false)]
theorem der_139800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139800 :=
  CNF.rup_sound cl_139800 [cl_139799,cl_107320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139799 v h) (hints_cons _ _ _ (der_107320 v h) (by intro d hd; cases hd)))
def cl_139801 : CNF.NClause := [(89,false),(84,true),(47,false)]
theorem der_139801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139801 :=
  CNF.rup_sound cl_139801 [cl_80134,cl_79460,cl_79471,cl_49788,cl_15872,cl_49869,cl_15867,cl_76637,cl_15874,cl_76590,cl_15894,cl_76636,cl_15878,cl_76570,cl_15886,cl_79642,cl_15870,cl_12656,cl_49804,cl_15887,cl_29847,cl_15877,cl_15671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80134 v h) (hints_cons _ _ _ (der_79460 v h) (hints_cons _ _ _ (der_79471 v h) (hints_cons _ _ _ (der_49788 v h) (hints_cons _ _ _ (der_15872 v h) (hints_cons _ _ _ (der_49869 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_76637 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_76590 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_76636 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_76570 v h) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_79642 v h) (hints_cons _ _ _ (der_15870 v h) (hints_cons _ _ _ (inp_12656 v h) (hints_cons _ _ _ (der_49804 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_29847 v h) (hints_cons _ _ _ (der_15877 v h) (hints_cons _ _ _ (der_15671 v h) (by intro d hd; cases hd))))))))))))))))))))))))
def cl_139802 : CNF.NClause := [(84,false),(75,true),(47,false)]
theorem der_139802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139802 :=
  CNF.rup_sound cl_139802 [cl_106044,cl_106043,cl_78418,cl_80133,cl_80128,cl_79460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106044 v h) (hints_cons _ _ _ (der_106043 v h) (hints_cons _ _ _ (der_78418 v h) (hints_cons _ _ _ (der_80133 v h) (hints_cons _ _ _ (der_80128 v h) (hints_cons _ _ _ (der_79460 v h) (by intro d hd; cases hd)))))))
def cl_139803 : CNF.NClause := [(75,true),(47,false)]
theorem der_139803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139803 :=
  CNF.rup_sound cl_139803 [cl_139802,cl_139801,cl_106043,cl_105744,cl_80129,cl_79460,cl_65888,cl_15911,cl_79662,cl_15915,cl_49788,cl_15912,cl_76637,cl_15914,cl_70711,cl_15913,cl_15741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139802 v h) (hints_cons _ _ _ (der_139801 v h) (hints_cons _ _ _ (der_106043 v h) (hints_cons _ _ _ (der_105744 v h) (hints_cons _ _ _ (der_80129 v h) (hints_cons _ _ _ (der_79460 v h) (hints_cons _ _ _ (der_65888 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_79662 v h) (hints_cons _ _ _ (der_15915 v h) (hints_cons _ _ _ (der_49788 v h) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_76637 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_70711 v h) (hints_cons _ _ _ (der_15913 v h) (hints_cons _ _ _ (der_15741 v h) (by intro d hd; cases hd))))))))))))))))))
def cl_139804 : CNF.NClause := [(77,false),(66,true),(47,false)]
theorem der_139804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139804 :=
  CNF.rup_sound cl_139804 [cl_139803,cl_80108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139803 v h) (hints_cons _ _ _ (der_80108 v h) (by intro d hd; cases hd)))
def cl_139805 : CNF.NClause := [(63,false),(86,true),(45,false)]
theorem der_139805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139805 :=
  CNF.rup_sound cl_139805 [cl_106036,cl_79457,cl_46318,cl_15918,cl_76622,cl_15924,cl_49825,cl_15928,cl_44225,cl_15907,cl_45685,cl_15911,cl_49968,cl_15934,cl_13695,cl_49816,cl_15917,cl_49819,cl_15919,cl_49802,cl_15916,cl_15739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106036 v h) (hints_cons _ _ _ (der_79457 v h) (hints_cons _ _ _ (der_46318 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_76622 v h) (hints_cons _ _ _ (der_15924 v h) (hints_cons _ _ _ (der_49825 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (der_44225 v h) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_45685 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_49968 v h) (hints_cons _ _ _ (der_15934 v h) (hints_cons _ _ _ (inp_13695 v h) (hints_cons _ _ _ (der_49816 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_49819 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_49802 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_15739 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139806 : CNF.NClause := [(86,false),(70,true),(45,false)]
theorem der_139806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139806 :=
  CNF.rup_sound cl_139806 [cl_80169,cl_79457,cl_46318,cl_15918,cl_49809,cl_15912,cl_76639,cl_15926,cl_49773,cl_15909,cl_76621,cl_15923,cl_79685,cl_15933,cl_13599,cl_49816,cl_15917,cl_49819,cl_15919,cl_49802,cl_15916,cl_15739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80169 v h) (hints_cons _ _ _ (der_79457 v h) (hints_cons _ _ _ (der_46318 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_49809 v h) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_76639 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (der_49773 v h) (hints_cons _ _ _ (der_15909 v h) (hints_cons _ _ _ (der_76621 v h) (hints_cons _ _ _ (der_15923 v h) (hints_cons _ _ _ (der_79685 v h) (hints_cons _ _ _ (der_15933 v h) (hints_cons _ _ _ (inp_13599 v h) (hints_cons _ _ _ (der_49816 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_49819 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_49802 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_15739 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139807 : CNF.NClause := [(63,true),(89,false),(45,false)]
theorem der_139807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139807 :=
  CNF.rup_sound cl_139807 [cl_80208,cl_79457,cl_44225,cl_15867,cl_45685,cl_15871,cl_76622,cl_15884,cl_49823,cl_15885,cl_42527,cl_15870,cl_49999,cl_15890,cl_53720,cl_15875,cl_15668,cl_49825,cl_15888,cl_49968,cl_15894,cl_12765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80208 v h) (hints_cons _ _ _ (der_79457 v h) (hints_cons _ _ _ (der_44225 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_45685 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_76622 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_49823 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_42527 v h) (hints_cons _ _ _ (der_15870 v h) (hints_cons _ _ _ (der_49999 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_53720 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_15668 v h) (hints_cons _ _ _ (der_49825 v h) (hints_cons _ _ _ (der_15888 v h) (hints_cons _ _ _ (der_49968 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (inp_12765 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139808 : CNF.NClause := [(86,false),(72,true),(45,false)]
theorem der_139808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139808 :=
  CNF.rup_sound cl_139808 [cl_106046,cl_79457,cl_76609,cl_15927,cl_46318,cl_15918,cl_49802,cl_15916,cl_49816,cl_15917,cl_49819,cl_15919,cl_15739,cl_49770,cl_15921,cl_76541,cl_15914,cl_76600,cl_15931,cl_76605,cl_15908,cl_13653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106046 v h) (hints_cons _ _ _ (der_79457 v h) (hints_cons _ _ _ (der_76609 v h) (hints_cons _ _ _ (der_15927 v h) (hints_cons _ _ _ (der_46318 v h) (hints_cons _ _ _ (der_15918 v h) (hints_cons _ _ _ (der_49802 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_49816 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_49819 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_49770 v h) (hints_cons _ _ _ (der_15921 v h) (hints_cons _ _ _ (der_76541 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_76600 v h) (hints_cons _ _ _ (der_15931 v h) (hints_cons _ _ _ (der_76605 v h) (hints_cons _ _ _ (der_15908 v h) (hints_cons _ _ _ (inp_13653 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139809 : CNF.NClause := [(70,false),(89,true),(45,false)]
theorem der_139809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139809 :=
  CNF.rup_sound cl_139809 [cl_80170,cl_79457,cl_76598,cl_15782,cl_49783,cl_15789,cl_37439,cl_15773,cl_49901,cl_15792,cl_15663,cl_49770,cl_15781,cl_76605,cl_15768,cl_76541,cl_15774,cl_76609,cl_15787,cl_76600,cl_15791,cl_8073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80170 v h) (hints_cons _ _ _ (der_79457 v h) (hints_cons _ _ _ (der_76598 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_49783 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_37439 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_49901 v h) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (der_49770 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_76605 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_76541 v h) (hints_cons _ _ _ (der_15774 v h) (hints_cons _ _ _ (der_76609 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_76600 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (inp_8073 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_139810 : CNF.NClause := [(86,true),(74,true),(60,false)]
theorem der_139810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139810 :=
  CNF.rup_sound cl_139810 [cl_105873,cl_105875,cl_105874,cl_79585,cl_80299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105873 v h) (hints_cons _ _ _ (der_105875 v h) (hints_cons _ _ _ (der_105874 v h) (hints_cons _ _ _ (der_79585 v h) (hints_cons _ _ _ (der_80299 v h) (by intro d hd; cases hd))))))
def cl_139811 : CNF.NClause := [(86,true),(68,true),(60,false)]
theorem der_139811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139811 :=
  CNF.rup_sound cl_139811 [cl_139810,cl_79846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139810 v h) (hints_cons _ _ _ (der_79846 v h) (by intro d hd; cases hd)))
def cl_139812 : CNF.NClause := [(88,false),(85,true),(52,false)]
theorem der_139812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139812 :=
  CNF.rup_sound cl_139812 [cl_139774,cl_80155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139774 v h) (hints_cons _ _ _ (der_80155 v h) (by intro d hd; cases hd)))
def cl_139813 : CNF.NClause := [(66,true),(52,false)]
theorem der_139813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139813 :=
  CNF.rup_sound cl_139813 [cl_139775,cl_80109,cl_79554,cl_49839,cl_15783,cl_49771,cl_15767,cl_43827,cl_15772,cl_49804,cl_15782,cl_49787,cl_15777,cl_15636,cl_76655,cl_15779,cl_49838,cl_15775,cl_49836,cl_15794,cl_15662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139775 v h) (hints_cons _ _ _ (der_80109 v h) (hints_cons _ _ _ (der_79554 v h) (hints_cons _ _ _ (der_49839 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_49771 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_43827 v h) (hints_cons _ _ _ (der_15772 v h) (hints_cons _ _ _ (der_49804 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_49787 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_15636 v h) (hints_cons _ _ _ (der_76655 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_49838 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_49836 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15662 v h) (by intro d hd; cases hd))))))))))))))))))))))
def cl_139814 : CNF.NClause := [(62,false),(69,true),(58,false)]
theorem der_139814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139814 :=
  CNF.rup_sound cl_139814 [cl_105846,cl_79502,cl_76648,cl_13737,cl_76613,cl_13834,cl_47172,cl_13845,cl_56890,cl_13843,cl_76847,cl_13836,cl_8387,cl_57423,cl_13849,cl_76625,cl_13833,cl_76640,cl_13835,cl_63467,cl_13827,cl_42519,cl_13842,cl_8424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105846 v h) (hints_cons _ _ _ (der_79502 v h) (hints_cons _ _ _ (der_76648 v h) (hints_cons _ _ _ (inp_13737 v h) (hints_cons _ _ _ (der_76613 v h) (hints_cons _ _ _ (inp_13834 v h) (hints_cons _ _ _ (der_47172 v h) (hints_cons _ _ _ (inp_13845 v h) (hints_cons _ _ _ (der_56890 v h) (hints_cons _ _ _ (inp_13843 v h) (hints_cons _ _ _ (der_76847 v h) (hints_cons _ _ _ (inp_13836 v h) (hints_cons _ _ _ (inp_8387 v h) (hints_cons _ _ _ (der_57423 v h) (hints_cons _ _ _ (inp_13849 v h) (hints_cons _ _ _ (der_76625 v h) (hints_cons _ _ _ (inp_13833 v h) (hints_cons _ _ _ (der_76640 v h) (hints_cons _ _ _ (inp_13835 v h) (hints_cons _ _ _ (der_63467 v h) (hints_cons _ _ _ (inp_13827 v h) (hints_cons _ _ _ (der_42519 v h) (hints_cons _ _ _ (inp_13842 v h) (hints_cons _ _ _ (inp_8424 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_139815 : CNF.NClause := [(69,false),(78,true),(58,false)]
theorem der_139815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139815 :=
  CNF.rup_sound cl_139815 [cl_79784,cl_79502,cl_76646,cl_13750,cl_76647,cl_14222,cl_79637,cl_14237,cl_79650,cl_14229,cl_43213,cl_14220,cl_10856,cl_57423,cl_14239,cl_42519,cl_14232,cl_76640,cl_14226,cl_76625,cl_14224,cl_63467,cl_14217,cl_10842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79784 v h) (hints_cons _ _ _ (der_79502 v h) (hints_cons _ _ _ (der_76646 v h) (hints_cons _ _ _ (inp_13750 v h) (hints_cons _ _ _ (der_76647 v h) (hints_cons _ _ _ (inp_14222 v h) (hints_cons _ _ _ (der_79637 v h) (hints_cons _ _ _ (inp_14237 v h) (hints_cons _ _ _ (der_79650 v h) (hints_cons _ _ _ (inp_14229 v h) (hints_cons _ _ _ (der_43213 v h) (hints_cons _ _ _ (inp_14220 v h) (hints_cons _ _ _ (inp_10856 v h) (hints_cons _ _ _ (der_57423 v h) (hints_cons _ _ _ (inp_14239 v h) (hints_cons _ _ _ (der_42519 v h) (hints_cons _ _ _ (inp_14232 v h) (hints_cons _ _ _ (der_76640 v h) (hints_cons _ _ _ (inp_14226 v h) (hints_cons _ _ _ (der_76625 v h) (hints_cons _ _ _ (inp_14224 v h) (hints_cons _ _ _ (der_63467 v h) (hints_cons _ _ _ (inp_14217 v h) (hints_cons _ _ _ (inp_10842 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_139816 : CNF.NClause := [(55,true),(91,false),(148,false)]
theorem der_139816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139816 :=
  CNF.rup_sound cl_139816 [cl_66108,cl_63761,cl_80957,cl_15790,cl_137960,cl_85704,cl_7041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66108 v h) (hints_cons _ _ _ (der_63761 v h) (hints_cons _ _ _ (der_80957 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_137960 v h) (hints_cons _ _ _ (der_85704 v h) (hints_cons _ _ _ (inp_7041 v h) (by intro d hd; cases hd))))))))
def cl_139817 : CNF.NClause := [(92,false),(41,true),(909,false),(76,false),(73,false)]
theorem der_139817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139817 :=
  CNF.rup_sound cl_139817 [cl_15876,cl_124819,cl_107219,cl_138122,cl_5249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_124819 v h) (hints_cons _ _ _ (der_107219 v h) (hints_cons _ _ _ (der_138122 v h) (hints_cons _ _ _ (inp_5249 v h) (by intro d hd; cases hd))))))
def cl_139819 : CNF.NClause := [(914,true),(918,true),(900,true),(910,true),(905,true),(917,true),(88,true)]
theorem der_139819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139819 :=
  CNF.rup_sound cl_139819 [cl_105706,cl_15671,cl_107244,cl_15685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105706 v h) (hints_cons _ _ _ (der_15671 v h) (hints_cons _ _ _ (der_107244 v h) (hints_cons _ _ _ (der_15685 v h) (by intro d hd; cases hd)))))
def cl_139820 : CNF.NClause := [(47,false),(16,true)]
theorem der_139820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139820 :=
  CNF.rup_sound cl_139820 [cl_79512,cl_139803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79512 v h) (hints_cons _ _ _ (der_139803 v h) (by intro d hd; cases hd)))
def cl_139821 : CNF.NClause := [(64,true),(33,false),(84,false)]
theorem der_139821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139821 :=
  CNF.rup_sound cl_139821 [cl_79955,cl_137994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79955 v h) (hints_cons _ _ _ (der_137994 v h) (by intro d hd; cases hd)))
def cl_139823 : CNF.NClause := [(83,true),(92,false),(36,false),(82,false)]
theorem der_139823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139823 :=
  CNF.rup_sound cl_139823 [cl_80248,cl_139773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80248 v h) (hints_cons _ _ _ (der_139773 v h) (by intro d hd; cases hd)))
def cl_139824 : CNF.NClause := [(83,true),(36,false),(92,false),(5,false)]
theorem der_139824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139824 :=
  CNF.rup_sound cl_139824 [cl_77645,cl_139773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77645 v h) (hints_cons _ _ _ (der_139773 v h) (by intro d hd; cases hd)))
def cl_139825 : CNF.NClause := [(85,true),(92,false),(5,false),(36,false)]
theorem der_139825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139825 :=
  CNF.rup_sound cl_139825 [cl_77656,cl_139773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77656 v h) (hints_cons _ _ _ (der_139773 v h) (by intro d hd; cases hd)))
def cl_139827 : CNF.NClause := [(86,true),(82,false),(5,false),(36,false)]
theorem der_139827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139827 :=
  CNF.rup_sound cl_139827 [cl_77673,cl_139773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77673 v h) (hints_cons _ _ _ (der_139773 v h) (by intro d hd; cases hd)))
def cl_139828 : CNF.NClause := [(92,true),(86,true),(36,false),(5,false)]
theorem der_139828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139828 :=
  CNF.rup_sound cl_139828 [cl_77675,cl_139773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77675 v h) (hints_cons _ _ _ (der_139773 v h) (by intro d hd; cases hd)))
def cl_139830 : CNF.NClause := [(35,false),(78,true)]
theorem der_139830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139830 :=
  CNF.rup_sound cl_139830 [cl_79480,cl_139771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79480 v h) (hints_cons _ _ _ (der_139771 v h) (by intro d hd; cases hd)))
def cl_139831 : CNF.NClause := [(35,false),(4,true)]
theorem der_139831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139831 :=
  CNF.rup_sound cl_139831 [cl_79577,cl_139830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79577 v h) (hints_cons _ _ _ (der_139830 v h) (by intro d hd; cases hd)))
def cl_139833 : CNF.NClause := [(83,true),(87,false),(35,false),(63,false)]
theorem der_139833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139833 :=
  CNF.rup_sound cl_139833 [cl_78228,cl_139830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78228 v h) (hints_cons _ _ _ (der_139830 v h) (by intro d hd; cases hd)))
def cl_139834 : CNF.NClause := [(40,false),(9,true)]
theorem der_139834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139834 :=
  CNF.rup_sound cl_139834 [cl_79532,cl_139770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79532 v h) (hints_cons _ _ _ (der_139770 v h) (by intro d hd; cases hd)))
def cl_139836 : CNF.NClause := [(52,false),(88,true)]
theorem der_139836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139836 :=
  CNF.rup_sound cl_139836 [cl_107264,cl_139813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107264 v h) (hints_cons _ _ _ (der_139813 v h) (by intro d hd; cases hd)))
def cl_139837 : CNF.NClause := [(52,false),(85,true)]
theorem der_139837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139837 :=
  CNF.rup_sound cl_139837 [cl_139812,cl_139836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139812 v h) (hints_cons _ _ _ (der_139836 v h) (by intro d hd; cases hd)))
def cl_139838 : CNF.NClause := [(54,false),(67,true)]
theorem der_139838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139838 :=
  CNF.rup_sound cl_139838 [cl_79487,cl_139778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79487 v h) (hints_cons _ _ _ (der_139778 v h) (by intro d hd; cases hd)))
def cl_139839 : CNF.NClause := [(64,true),(1076,false)]
theorem der_139839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139839 :=
  CNF.rup_sound cl_139839 [cl_98046,cl_137966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98046 v h) (hints_cons _ _ _ (der_137966 v h) (by intro d hd; cases hd)))
def cl_139840 : CNF.NClause := [(70,true),(130,false)]
theorem der_139840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139840 :=
  CNF.rup_sound cl_139840 [cl_138023,cl_57480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138023 v h) (hints_cons _ _ _ (der_57480 v h) (by intro d hd; cases hd)))
def cl_139841 : CNF.NClause := [(131,false),(82,true)]
theorem der_139841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139841 :=
  CNF.rup_sound cl_139841 [cl_138040,cl_57263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138040 v h) (hints_cons _ _ _ (der_57263 v h) (by intro d hd; cases hd)))
def cl_139842 : CNF.NClause := [(91,true),(78,false),(37,false)]
theorem der_139842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139842 :=
  CNF.rup_sound cl_139842 [cl_77046,cl_139784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77046 v h) (hints_cons _ _ _ (der_139784 v h) (by intro d hd; cases hd)))
def cl_139843 : CNF.NClause := [(91,true),(37,false),(6,true)]
theorem der_139843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139843 :=
  CNF.rup_sound cl_139843 [cl_138043,cl_139842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138043 v h) (hints_cons _ _ _ (der_139842 v h) (by intro d hd; cases hd)))
def cl_139844 : CNF.NClause := [(89,true),(58,false),(62,false)]
theorem der_139844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139844 :=
  CNF.rup_sound cl_139844 [cl_107321,cl_139814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107321 v h) (hints_cons _ _ _ (der_139814 v h) (by intro d hd; cases hd)))
def cl_139845 : CNF.NClause := [(85,true),(58,false),(62,false)]
theorem der_139845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139845 :=
  CNF.rup_sound cl_139845 [cl_105848,cl_139814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105848 v h) (hints_cons _ _ _ (der_139814 v h) (by intro d hd; cases hd)))
def cl_139846 : CNF.NClause := [(76,true),(58,false),(69,false)]
theorem der_139846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139846 :=
  CNF.rup_sound cl_139846 [cl_105849,cl_139815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105849 v h) (hints_cons _ _ _ (der_139815 v h) (by intro d hd; cases hd)))
def cl_139847 : CNF.NClause := [(50,false),(63,true),(74,false)]
theorem der_139847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139847 :=
  CNF.rup_sound cl_139847 [cl_80063,cl_139777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80063 v h) (hints_cons _ _ _ (der_139777 v h) (by intro d hd; cases hd)))
def cl_139848 : CNF.NClause := [(90,true),(71,false),(50,false)]
theorem der_139848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139848 :=
  CNF.rup_sound cl_139848 [cl_106028,cl_139777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106028 v h) (hints_cons _ _ _ (der_139777 v h) (by intro d hd; cases hd)))
def cl_139849 : CNF.NClause := [(50,false),(77,false),(74,true)]
theorem der_139849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139849 :=
  CNF.rup_sound cl_139849 [cl_80074,cl_139777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80074 v h) (hints_cons _ _ _ (der_139777 v h) (by intro d hd; cases hd)))
def cl_139851 : CNF.NClause := [(50,false),(77,true),(63,false)]
theorem der_139851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139851 :=
  CNF.rup_sound cl_139851 [cl_80076,cl_139777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80076 v h) (hints_cons _ _ _ (der_139777 v h) (by intro d hd; cases hd)))
def cl_139852 : CNF.NClause := [(90,true),(63,true),(50,false)]
theorem der_139852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139852 :=
  CNF.rup_sound cl_139852 [cl_80077,cl_139777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80077 v h) (hints_cons _ _ _ (der_139777 v h) (by intro d hd; cases hd)))
def cl_139853 : CNF.NClause := [(82,true),(37,false),(74,false)]
theorem der_139853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139853 :=
  CNF.rup_sound cl_139853 [cl_80194,cl_139782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80194 v h) (hints_cons _ _ _ (der_139782 v h) (by intro d hd; cases hd)))
def cl_139854 : CNF.NClause := [(70,true),(37,false),(82,false)]
theorem der_139854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139854 :=
  CNF.rup_sound cl_139854 [cl_80202,cl_139784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80202 v h) (hints_cons _ _ _ (der_139784 v h) (by intro d hd; cases hd)))
def cl_139855 : CNF.NClause := [(6,true),(74,false),(37,false)]
theorem der_139855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139855 :=
  CNF.rup_sound cl_139855 [cl_49711,cl_139843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49711 v h) (hints_cons _ _ _ (der_139843 v h) (by intro d hd; cases hd)))
def cl_139856 : CNF.NClause := [(63,true),(1068,false),(1078,true)]
theorem der_139856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139856 :=
  CNF.rup_sound cl_139856 [cl_138064,cl_124863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138064 v h) (hints_cons _ _ _ (der_124863 v h) (by intro d hd; cases hd)))
def cl_139857 : CNF.NClause := [(51,false),(68,false),(20,true)]
theorem der_139857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139857 :=
  CNF.rup_sound cl_139857 [cl_79566,cl_139794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79566 v h) (hints_cons _ _ _ (der_139794 v h) (by intro d hd; cases hd)))
def cl_139858 : CNF.NClause := [(51,false),(20,true),(69,false)]
theorem der_139858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139858 :=
  CNF.rup_sound cl_139858 [cl_79567,cl_139857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79567 v h) (hints_cons _ _ _ (der_139857 v h) (by intro d hd; cases hd)))
def cl_139859 : CNF.NClause := [(133,false),(88,false),(40,true)]
theorem der_139859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139859 :=
  CNF.rup_sound cl_139859 [cl_138065,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138065 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_139860 : CNF.NClause := [(76,true),(82,true),(8,false)]
theorem der_139860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139860 :=
  CNF.rup_sound cl_139860 [cl_138066,cl_76592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138066 v h) (hints_cons _ _ _ (der_76592 v h) (by intro d hd; cases hd)))
def cl_139862 : CNF.NClause := [(126,false),(4,false),(33,true)]
theorem der_139862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139862 :=
  CNF.rup_sound cl_139862 [cl_138068,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138068 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_139863 : CNF.NClause := [(126,false),(87,false),(33,true)]
theorem der_139863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139863 :=
  CNF.rup_sound cl_139863 [cl_138070,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138070 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_139865 : CNF.NClause := [(133,false),(40,true),(13,false)]
theorem der_139865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139865 :=
  CNF.rup_sound cl_139865 [cl_138073,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138073 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_139866 : CNF.NClause := [(140,false),(47,true),(14,false)]
theorem der_139866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139866 :=
  CNF.rup_sound cl_139866 [cl_138075,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138075 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_139867 : CNF.NClause := [(71,true),(62,true),(26,false)]
theorem der_139867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139867 :=
  CNF.rup_sound cl_139867 [cl_138076,cl_29835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138076 v h) (hints_cons _ _ _ (der_29835 v h) (by intro d hd; cases hd)))
def cl_139868 : CNF.NClause := [(53,false),(78,false),(67,true)]
theorem der_139868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139868 :=
  CNF.rup_sound cl_139868 [cl_138079,cl_139776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138079 v h) (hints_cons _ _ _ (der_139776 v h) (by intro d hd; cases hd)))
def cl_139869 : CNF.NClause := [(140,false),(47,true),(89,false)]
theorem der_139869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139869 :=
  CNF.rup_sound cl_139869 [cl_138081,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138081 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_139870 : CNF.NClause := [(150,false),(57,true),(24,false)]
theorem der_139870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139870 :=
  CNF.rup_sound cl_139870 [cl_138086,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138086 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_139872 : CNF.NClause := [(145,false),(133,false),(119,true)]
theorem der_139872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139872 :=
  CNF.rup_sound cl_139872 [cl_138088,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138088 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_139873 : CNF.NClause := [(85,true),(918,false),(902,true)]
theorem der_139873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139873 :=
  CNF.rup_sound cl_139873 [cl_138089,cl_123214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138089 v h) (hints_cons _ _ _ (der_123214 v h) (by intro d hd; cases hd)))
def cl_139874 : CNF.NClause := [(142,false),(49,true),(24,false)]
theorem der_139874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139874 :=
  CNF.rup_sound cl_139874 [cl_138093,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138093 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_139875 : CNF.NClause := [(70,true),(51,false),(68,false)]
theorem der_139875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139875 :=
  CNF.rup_sound cl_139875 [cl_138095,cl_139794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138095 v h) (hints_cons _ _ _ (der_139794 v h) (by intro d hd; cases hd)))
def cl_139876 : CNF.NClause := [(63,true),(1068,false),(1063,true)]
theorem der_139876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139876 :=
  CNF.rup_sound cl_139876 [cl_138096,cl_137967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138096 v h) (hints_cons _ _ _ (der_137967 v h) (by intro d hd; cases hd)))
def cl_139877 : CNF.NClause := [(150,false),(57,true),(18,false)]
theorem der_139877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139877 :=
  CNF.rup_sound cl_139877 [cl_138098,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138098 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_139878 : CNF.NClause := [(51,false),(68,false),(20,true)]
theorem der_139878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139878 :=
  CNF.rup_sound cl_139878 [cl_124899,cl_139875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124899 v h) (hints_cons _ _ _ (der_139875 v h) (by intro d hd; cases hd)))
def cl_139879 : CNF.NClause := [(128,false),(126,false),(118,true)]
theorem der_139879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139879 :=
  CNF.rup_sound cl_139879 [cl_138105,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138105 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_139880 : CNF.NClause := [(128,false),(68,true),(140,true)]
theorem der_139880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139880 :=
  CNF.rup_sound cl_139880 [cl_138106,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138106 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_139881 : CNF.NClause := [(92,true),(36,false),(5,false)]
theorem der_139881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139881 :=
  CNF.rup_sound cl_139881 [cl_139828,cl_139800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139828 v h) (hints_cons _ _ _ (der_139800 v h) (by intro d hd; cases hd)))
def cl_139882 : CNF.NClause := [(83,true),(87,false),(35,false)]
theorem der_139882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139882 :=
  CNF.rup_sound cl_139882 [cl_139833,cl_139772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_139833 v h) (hints_cons _ _ _ (der_139772 v h) (by intro d hd; cases hd)))
def cl_139884 : CNF.NClause := [(78,false),(74,true),(37,false),(82,false)]
theorem der_139884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139884 :=
  CNF.rup_sound cl_139884 [cl_77619,cl_139781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77619 v h) (hints_cons _ _ _ (der_139781 v h) (by intro d hd; cases hd)))
def cl_139888 : CNF.NClause := [(69,true),(78,false),(89,false),(58,false)]
theorem der_139888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139888 :=
  CNF.rup_sound cl_139888 [cl_50743,cl_139814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50743 v h) (hints_cons _ _ _ (der_139814 v h) (by intro d hd; cases hd)))
def cl_139891 : CNF.NClause := [(68,true),(62,false),(60,false),(29,true)]
theorem der_139891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139891 :=
  CNF.rup_sound cl_139891 [cl_80292,cl_139811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80292 v h) (hints_cons _ _ _ (der_139811 v h) (by intro d hd; cases hd)))
def cl_139893 : CNF.NClause := [(74,true),(29,true),(60,false),(68,true)]
theorem der_139893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139893 :=
  CNF.rup_sound cl_139893 [cl_106129,cl_139810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106129 v h) (hints_cons _ _ _ (der_139810 v h) (by intro d hd; cases hd)))
def cl_139894 : CNF.NClause := [(86,true),(62,false),(60,false),(29,false)]
theorem der_139894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139894 :=
  CNF.rup_sound cl_139894 [cl_77855,cl_139810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77855 v h) (hints_cons _ _ _ (der_139810 v h) (by intro d hd; cases hd)))
def cl_139895 : CNF.NClause := [(80,true),(86,true),(60,false),(62,false)]
theorem der_139895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139895 :=
  CNF.rup_sound cl_139895 [cl_138109,cl_139810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138109 v h) (hints_cons _ _ _ (der_139810 v h) (by intro d hd; cases hd)))
def cl_139896 : CNF.NClause := [(68,true),(60,false),(62,false),(74,false)]
theorem der_139896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139896 :=
  CNF.rup_sound cl_139896 [cl_50866,cl_139891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50866 v h) (hints_cons _ _ _ (der_139891 v h) (by intro d hd; cases hd)))
def cl_139897 : CNF.NClause := [(69,true),(90,false),(42,false),(83,false)]
theorem der_139897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139897 :=
  CNF.rup_sound cl_139897 [cl_77950,cl_138051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77950 v h) (hints_cons _ _ _ (der_138051 v h) (by intro d hd; cases hd)))
def cl_139898 : CNF.NClause := [(69,true),(66,false),(90,false),(42,false)]
theorem der_139898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139898 :=
  CNF.rup_sound cl_139898 [cl_77954,cl_138100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77954 v h) (hints_cons _ _ _ (der_138100 v h) (by intro d hd; cases hd)))
def cl_139899 : CNF.NClause := [(90,true),(83,true),(42,false),(69,false)]
theorem der_139899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139899 :=
  CNF.rup_sound cl_139899 [cl_77983,cl_139797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77983 v h) (hints_cons _ _ _ (der_139797 v h) (by intro d hd; cases hd)))
def cl_139900 : CNF.NClause := [(73,true),(59,false),(62,false),(70,false)]
theorem der_139900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139900 :=
  CNF.rup_sound cl_139900 [cl_80380,cl_139788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80380 v h) (hints_cons _ _ _ (der_139788 v h) (by intro d hd; cases hd)))
def cl_139901 : CNF.NClause := [(87,false),(68,true),(73,false),(35,false)]
theorem der_139901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139901 :=
  CNF.rup_sound cl_139901 [cl_78224,cl_139882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78224 v h) (hints_cons _ _ _ (der_139882 v h) (by intro d hd; cases hd)))
def cl_139902 : CNF.NClause := [(73,false),(4,false),(35,false),(87,true)]
theorem der_139902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139902 :=
  CNF.rup_sound cl_139902 [cl_78255,cl_139796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78255 v h) (hints_cons _ _ _ (der_139796 v h) (by intro d hd; cases hd)))
def cl_139904 : CNF.NClause := [(92,true),(69,true),(51,false),(70,false)]
theorem der_139904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139904 :=
  CNF.rup_sound cl_139904 [cl_51404,cl_139795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51404 v h) (hints_cons _ _ _ (der_139795 v h) (by intro d hd; cases hd)))
def cl_139905 : CNF.NClause := [(69,true),(67,true),(68,true),(51,false)]
theorem der_139905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139905 :=
  CNF.rup_sound cl_139905 [cl_78322,cl_139795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78322 v h) (hints_cons _ _ _ (der_139795 v h) (by intro d hd; cases hd)))
def cl_139906 : CNF.NClause := [(71,true),(81,true),(32,false),(66,false)]
theorem der_139906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139906 :=
  CNF.rup_sound cl_139906 [cl_51486,cl_138059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51486 v h) (hints_cons _ _ _ (der_138059 v h) (by intro d hd; cases hd)))
def cl_139907 : CNF.NClause := [(86,true),(1,false),(66,false),(32,false)]
theorem der_139907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139907 :=
  CNF.rup_sound cl_139907 [cl_78384,cl_138102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78384 v h) (hints_cons _ _ _ (der_138102 v h) (by intro d hd; cases hd)))
def cl_139908 : CNF.NClause := [(66,false),(1,true),(32,false),(71,true)]
theorem der_139908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139908 :=
  CNF.rup_sound cl_139908 [cl_80396,cl_139906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80396 v h) (hints_cons _ _ _ (der_139906 v h) (by intro d hd; cases hd)))
def cl_139910 : CNF.NClause := [(71,true),(76,true),(32,false),(81,true)]
theorem der_139910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139910 :=
  CNF.rup_sound cl_139910 [cl_51499,cl_139906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51499 v h) (hints_cons _ _ _ (der_139906 v h) (by intro d hd; cases hd)))
def cl_139911 : CNF.NClause := [(77,true),(47,false),(89,false),(16,false)]
theorem der_139911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139911 :=
  CNF.rup_sound cl_139911 [cl_78418,cl_139801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78418 v h) (hints_cons _ _ _ (der_139801 v h) (by intro d hd; cases hd)))
def cl_139913 : CNF.NClause := [(79,true),(89,false),(45,false),(70,false)]
theorem der_139913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139913 :=
  CNF.rup_sound cl_139913 [cl_80401,cl_139807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80401 v h) (hints_cons _ _ _ (der_139807 v h) (by intro d hd; cases hd)))
def cl_139914 : CNF.NClause := [(89,true),(72,false),(45,false),(63,true)]
theorem der_139914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139914 :=
  CNF.rup_sound cl_139914 [cl_51898,cl_139809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51898 v h) (hints_cons _ _ _ (der_139809 v h) (by intro d hd; cases hd)))
def cl_139915 : CNF.NClause := [(78,true),(66,false),(6,true),(37,false)]
theorem der_139915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139915 :=
  CNF.rup_sound cl_139915 [cl_49708,cl_139855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49708 v h) (hints_cons _ _ _ (der_139855 v h) (by intro d hd; cases hd)))
def cl_139917 : CNF.NClause := [(77,true),(68,true),(16,false),(4,true)]
theorem der_139917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139917 :=
  CNF.rup_sound cl_139917 [cl_138118,cl_41231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138118 v h) (hints_cons _ _ _ (der_41231 v h) (by intro d hd; cases hd)))
def cl_139919 : CNF.NClause := [(70,true),(916,false),(919,true),(927,true)]
theorem der_139919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139919 :=
  CNF.rup_sound cl_139919 [cl_138120,cl_115995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138120 v h) (hints_cons _ _ _ (der_115995 v h) (by intro d hd; cases hd)))
def cl_139920 : CNF.NClause := [(131,false),(38,true),(915,true),(906,false)]
theorem der_139920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139920 :=
  CNF.rup_sound cl_139920 [cl_138127,cl_139841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138127 v h) (hints_cons _ _ _ (der_139841 v h) (by intro d hd; cases hd)))
def cl_139921 : CNF.NClause := [(150,false),(71,false),(57,true),(91,false)]
theorem der_139921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139921 :=
  CNF.rup_sound cl_139921 [cl_138128,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138128 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_139922 : CNF.NClause := [(129,false),(10,false),(82,false),(36,true)]
theorem der_139922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139922 :=
  CNF.rup_sound cl_139922 [cl_138129,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138129 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_139924 : CNF.NClause := [(127,false),(87,false),(70,false),(34,true)]
theorem der_139924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139924 :=
  CNF.rup_sound cl_139924 [cl_138132,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138132 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_139925 : CNF.NClause := [(80,true),(1065,true),(1057,true),(1061,false)]
theorem der_139925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139925 :=
  CNF.rup_sound cl_139925 [cl_138133,cl_116107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138133 v h) (hints_cons _ _ _ (der_116107 v h) (by intro d hd; cases hd)))
def cl_139926 : CNF.NClause := [(150,false),(71,false),(24,false),(57,true)]
theorem der_139926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139926 :=
  CNF.rup_sound cl_139926 [cl_138134,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138134 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_139927 : CNF.NClause := [(39,false),(150,false),(57,true),(55,false)]
theorem der_139927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139927 :=
  CNF.rup_sound cl_139927 [cl_138135,cl_88593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138135 v h) (hints_cons _ _ _ (der_88593 v h) (by intro d hd; cases hd)))
def cl_139928 : CNF.NClause := [(118,false),(126,false),(33,true),(68,false)]
theorem der_139928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139928 :=
  CNF.rup_sound cl_139928 [cl_138136,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138136 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_139931 : CNF.NClause := [(86,true),(1083,false),(1055,true),(1076,true)]
theorem der_139931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139931 :=
  CNF.rup_sound cl_139931 [cl_138144,cl_118251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138144 v h) (hints_cons _ _ _ (der_118251 v h) (by intro d hd; cases hd)))
def cl_139932 : CNF.NClause := [(69,false),(89,false),(62,true),(58,false)]
theorem der_139932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139932 :=
  CNF.rup_sound cl_139932 [cl_138145,cl_139846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138145 v h) (hints_cons _ _ _ (der_139846 v h) (by intro d hd; cases hd)))
def cl_139933 : CNF.NClause := [(42,false),(90,true),(69,false),(132,true)]
theorem der_139933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139933 :=
  CNF.rup_sound cl_139933 [cl_127221,cl_139899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127221 v h) (hints_cons _ _ _ (der_139899 v h) (by intro d hd; cases hd)))
def cl_139934 : CNF.NClause := [(71,true),(86,false),(66,false),(32,false)]
theorem der_139934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139934 :=
  CNF.rup_sound cl_139934 [cl_138146,cl_80089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138146 v h) (hints_cons _ _ _ (der_80089 v h) (by intro d hd; cases hd)))
def cl_139935 : CNF.NClause := [(120,true),(47,false),(131,true),(140,true)]
theorem der_139935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139935 :=
  CNF.rup_sound cl_139935 [cl_138147,cl_139820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138147 v h) (hints_cons _ _ _ (der_139820 v h) (by intro d hd; cases hd)))
def cl_139936 : CNF.NClause := [(136,false),(150,false),(152,true),(64,false),(122,true)]
theorem der_139936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139936 :=
  CNF.rup_sound cl_139936 [cl_138154,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138154 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_139938 : CNF.NClause := [(141,false),(77,false),(9,false),(48,true),(70,false)]
theorem der_139938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139938 :=
  CNF.rup_sound cl_139938 [cl_138158,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138158 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_139939 : CNF.NClause := [(130,false),(122,true),(80,false),(63,false),(148,false)]
theorem der_139939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139939 :=
  CNF.rup_sound cl_139939 [cl_138166,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138166 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_139940 : CNF.NClause := [(140,false),(47,true),(77,false),(139,true),(120,false)]
theorem der_139940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139940 :=
  CNF.rup_sound cl_139940 [cl_138172,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138172 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_139941 : CNF.NClause := [(905,false),(37,true),(82,false),(78,false),(66,false)]
theorem der_139941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139941 :=
  CNF.rup_sound cl_139941 [cl_138173,cl_137958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138173 v h) (hints_cons _ _ _ (der_137958 v h) (by intro d hd; cases hd)))
def cl_139942 : CNF.NClause := [(151,false),(119,false),(48,true),(77,false),(141,false)]
theorem der_139942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139942 :=
  CNF.rup_sound cl_139942 [cl_138182,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138182 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_139943 : CNF.NClause := [(52,true),(920,false),(85,false),(73,false),(66,false)]
theorem der_139943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139943 :=
  CNF.rup_sound cl_139943 [cl_138184,cl_133089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138184 v h) (hints_cons _ _ _ (der_133089 v h) (by intro d hd; cases hd)))
def cl_139944 : CNF.NClause := [(925,false),(6,false),(79,false),(62,false),(57,true)]
theorem der_139944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139944 :=
  CNF.rup_sound cl_139944 [cl_138189,cl_116082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138189 v h) (hints_cons _ _ _ (der_116082 v h) (by intro d hd; cases hd)))
def cl_139945 : CNF.NClause := [(144,false),(148,false),(133,false),(55,true),(122,false)]
theorem der_139945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139945 :=
  CNF.rup_sound cl_139945 [cl_138196,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138196 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_139946 : CNF.NClause := [(35,false),(128,true),(85,false),(126,true),(118,true)]
theorem der_139946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139946 :=
  CNF.rup_sound cl_139946 [cl_134774,cl_139831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134774 v h) (hints_cons _ _ _ (der_139831 v h) (by intro d hd; cases hd)))
def cl_139947 : CNF.NClause := [(126,false),(125,false),(7,true),(143,true),(33,true),(32,true)]
theorem der_139947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139947 :=
  CNF.rup_sound cl_139947 [cl_138204,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138204 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_139948 : CNF.NClause := [(151,false),(136,false),(88,false),(152,true),(35,false),(99,true)]
theorem der_139948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139948 :=
  CNF.rup_sound cl_139948 [cl_138212,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138212 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_139949 : CNF.NClause := [(905,false),(37,true),(74,false),(78,false),(66,false),(907,true)]
theorem der_139949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139949 :=
  CNF.rup_sound cl_139949 [cl_138213,cl_115995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138213 v h) (hints_cons _ _ _ (der_115995 v h) (by intro d hd; cases hd)))
def cl_139950 : CNF.NClause := [(55,true),(6,false),(80,false),(63,false),(923,false),(912,true)]
theorem der_139950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139950 :=
  CNF.rup_sound cl_139950 [cl_138255,cl_137963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138255 v h) (hints_cons _ _ _ (der_137963 v h) (by intro d hd; cases hd)))
def cl_139951 : CNF.NClause := [(55,true),(148,false),(143,true),(6,false),(138,true),(128,true)]
theorem der_139951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139951 :=
  CNF.rup_sound cl_139951 [cl_138260,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138260 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_139954 : CNF.NClause := [(925,false),(7,true),(79,false),(12,false),(57,true),(62,false)]
theorem der_139954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139954 :=
  CNF.rup_sound cl_139954 [cl_138295,cl_116082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138295 v h) (hints_cons _ _ _ (der_116082 v h) (by intro d hd; cases hd)))
def cl_139955 : CNF.NClause := [(39,false),(134,false),(37,false),(122,false),(101,false),(97,false)]
theorem der_139955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139955 :=
  CNF.rup_sound cl_139955 [cl_138307,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138307 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_139956 : CNF.NClause := [(21,false),(48,true),(141,false),(88,false),(70,false),(83,false)]
theorem der_139956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139956 :=
  CNF.rup_sound cl_139956 [cl_138322,cl_79619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138322 v h) (hints_cons _ _ _ (der_79619 v h) (by intro d hd; cases hd)))
def cl_139957 : CNF.NClause := [(137,false),(153,false),(59,false),(121,false),(104,false),(101,false),(112,false)]
theorem der_139957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139957 :=
  CNF.rup_sound cl_139957 [cl_138327,cl_57227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138327 v h) (hints_cons _ _ _ (der_57227 v h) (by intro d hd; cases hd)))
def cl_139959 : CNF.NClause := [(146,false),(152,false),(38,false),(120,false),(111,false),(113,false),(102,false)]
theorem der_139959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139959 :=
  CNF.rup_sound cl_139959 [cl_138332,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138332 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_139960 : CNF.NClause := [(146,false),(152,false),(120,false),(47,false),(99,false),(108,false),(97,false)]
theorem der_139960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139960 :=
  CNF.rup_sound cl_139960 [cl_138333,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138333 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_139961 : CNF.NClause := [(146,false),(152,false),(55,false),(122,false),(94,false),(111,false),(107,false)]
theorem der_139961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139961 :=
  CNF.rup_sound cl_139961 [cl_138334,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138334 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_139962 : CNF.NClause := [(144,false),(129,false),(38,false),(120,false),(111,false),(104,false),(95,false)]
theorem der_139962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139962 :=
  CNF.rup_sound cl_139962 [cl_138335,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138335 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_139963 : CNF.NClause := [(127,false),(125,false),(58,false),(120,false),(100,false),(109,false),(93,false)]
theorem der_139963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139963 :=
  CNF.rup_sound cl_139963 [cl_138337,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138337 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_139964 : CNF.NClause := [(127,false),(125,false),(120,false),(47,false),(99,false),(108,false),(115,false)]
theorem der_139964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139964 :=
  CNF.rup_sound cl_139964 [cl_138339,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138339 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_139965 : CNF.NClause := [(128,false),(126,false),(132,false),(135,false),(50,false),(37,false),(104,false)]
theorem der_139965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139965 :=
  CNF.rup_sound cl_139965 [cl_138340,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138340 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_139966 : CNF.NClause := [(144,false),(129,false),(35,false),(118,false),(94,false),(104,false),(109,false)]
theorem der_139966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139966 :=
  CNF.rup_sound cl_139966 [cl_138341,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138341 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_139968 : CNF.NClause := [(152,false),(135,false),(118,false),(33,false),(110,false),(105,false),(95,false)]
theorem der_139968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139968 :=
  CNF.rup_sound cl_139968 [cl_138346,cl_85856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138346 v h) (hints_cons _ _ _ (der_85856 v h) (by intro d hd; cases hd)))
def cl_139969 : CNF.NClause := [(144,false),(139,false),(38,false),(45,false),(49,false),(37,false),(112,false)]
theorem der_139969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139969 :=
  CNF.rup_sound cl_139969 [cl_138347,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138347 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_139970 : CNF.NClause := [(128,false),(126,false),(60,false),(119,false),(111,false),(117,false),(93,false)]
theorem der_139970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139970 :=
  CNF.rup_sound cl_139970 [cl_138348,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138348 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_139971 : CNF.NClause := [(128,false),(144,false),(126,false),(129,false),(43,false),(37,false),(32,false)]
theorem der_139971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139971 :=
  CNF.rup_sound cl_139971 [cl_138349,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138349 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_139972 : CNF.NClause := [(128,false),(136,false),(148,false),(33,false),(110,false),(100,false),(105,false)]
theorem der_139972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139972 :=
  CNF.rup_sound cl_139972 [cl_138350,cl_107182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138350 v h) (hints_cons _ _ _ (der_107182 v h) (by intro d hd; cases hd)))
def cl_139973 : CNF.NClause := [(129,false),(139,false),(59,false),(121,false),(104,false),(101,false),(93,false)]
theorem der_139973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139973 :=
  CNF.rup_sound cl_139973 [cl_138351,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138351 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_139974 : CNF.NClause := [(146,false),(152,false),(43,false),(37,false),(55,false),(104,false),(93,false)]
theorem der_139974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139974 :=
  CNF.rup_sound cl_139974 [cl_138352,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138352 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_139975 : CNF.NClause := [(128,false),(126,false),(152,false),(135,false),(50,false),(38,false),(45,false)]
theorem der_139975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139975 :=
  CNF.rup_sound cl_139975 [cl_138357,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138357 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_139976 : CNF.NClause := [(128,false),(126,false),(38,false),(120,false),(111,false),(113,false),(102,false)]
theorem der_139976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139976 :=
  CNF.rup_sound cl_139976 [cl_138358,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138358 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_139977 : CNF.NClause := [(137,false),(145,false),(51,false),(99,false),(100,false),(101,false),(123,false)]
theorem der_139977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139977 :=
  CNF.rup_sound cl_139977 [cl_138361,cl_88561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138361 v h) (hints_cons _ _ _ (der_88561 v h) (by intro d hd; cases hd)))
def cl_139978 : CNF.NClause := [(134,false),(139,false),(37,false),(122,false),(113,false),(101,false),(97,false)]
theorem der_139978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139978 :=
  CNF.rup_sound cl_139978 [cl_138362,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138362 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_139979 : CNF.NClause := [(153,false),(133,false),(43,false),(122,false),(116,false),(95,false),(103,false)]
theorem der_139979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139979 :=
  CNF.rup_sound cl_139979 [cl_138363,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138363 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_139980 : CNF.NClause := [(138,false),(151,false),(51,false),(99,false),(123,false),(102,false),(98,false)]
theorem der_139980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139980 :=
  CNF.rup_sound cl_139980 [cl_138365,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138365 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_139981 : CNF.NClause := [(66,true),(79,false),(88,false),(73,false),(67,false),(1075,false),(1070,true)]
theorem der_139981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139981 :=
  CNF.rup_sound cl_139981 [cl_138366,cl_139813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138366 v h) (hints_cons _ _ _ (der_139813 v h) (by intro d hd; cases hd)))
def cl_139982 : CNF.NClause := [(136,false),(39,false),(130,false),(42,false),(59,false),(60,false),(44,false)]
theorem der_139982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139982 :=
  CNF.rup_sound cl_139982 [cl_138367,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138367 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_139983 : CNF.NClause := [(153,false),(45,false),(141,false),(37,false),(58,false),(34,false),(99,false)]
theorem der_139983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139983 :=
  CNF.rup_sound cl_139983 [cl_138374,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138374 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_139984 : CNF.NClause := [(140,false),(131,false),(48,false),(119,false),(114,false),(101,false),(107,false)]
theorem der_139984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139984 :=
  CNF.rup_sound cl_139984 [cl_138375,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138375 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_139985 : CNF.NClause := [(133,false),(52,false),(34,false),(118,false),(111,false),(96,false),(101,false)]
theorem der_139985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139985 :=
  CNF.rup_sound cl_139985 [cl_138377,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138377 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_139986 : CNF.NClause := [(147,false),(140,false),(50,false),(121,false),(94,false),(116,false),(102,false)]
theorem der_139986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139986 :=
  CNF.rup_sound cl_139986 [cl_138381,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138381 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_139987 : CNF.NClause := [(137,false),(133,false),(45,false),(120,false),(110,false),(101,false),(117,false)]
theorem der_139987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139987 :=
  CNF.rup_sound cl_139987 [cl_138383,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138383 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_139988 : CNF.NClause := [(132,false),(135,false),(116,false),(123,false),(117,false),(36,false),(115,false)]
theorem der_139988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139988 :=
  CNF.rup_sound cl_139988 [cl_138385,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138385 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_139989 : CNF.NClause := [(140,false),(131,false),(34,false),(118,false),(96,false),(101,false),(116,false)]
theorem der_139989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139989 :=
  CNF.rup_sound cl_139989 [cl_138387,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138387 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_139991 : CNF.NClause := [(137,false),(101,false),(39,false),(47,false),(114,false),(141,false),(95,false)]
theorem der_139991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139991 :=
  CNF.rup_sound cl_139991 [cl_138389,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138389 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_139993 : CNF.NClause := [(138,false),(131,false),(129,false),(139,false),(35,false),(118,false),(99,false)]
theorem der_139993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139993 :=
  CNF.rup_sound cl_139993 [cl_138392,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138392 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_139994 : CNF.NClause := [(129,false),(134,false),(44,false),(119,false),(96,false),(102,false),(109,false)]
theorem der_139994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139994 :=
  CNF.rup_sound cl_139994 [cl_138394,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138394 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_139995 : CNF.NClause := [(137,false),(133,false),(50,false),(53,false),(49,false),(54,false),(113,false)]
theorem der_139995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139995 :=
  CNF.rup_sound cl_139995 [cl_138395,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138395 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_139996 : CNF.NClause := [(145,false),(133,false),(120,false),(54,false),(96,false),(114,false),(105,false)]
theorem der_139996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139996 :=
  CNF.rup_sound cl_139996 [cl_138396,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138396 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_139997 : CNF.NClause := [(138,false),(144,false),(129,false),(54,false),(118,false),(33,false),(95,false)]
theorem der_139997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139997 :=
  CNF.rup_sound cl_139997 [cl_138398,cl_139778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138398 v h) (hints_cons _ _ _ (der_139778 v h) (by intro d hd; cases hd)))
def cl_139998 : CNF.NClause := [(128,false),(39,false),(126,false),(59,false),(50,false),(53,false),(57,false)]
theorem der_139998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139998 :=
  CNF.rup_sound cl_139998 [cl_138402,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138402 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_139999 : CNF.NClause := [(137,false),(133,false),(120,false),(47,false),(99,false),(108,false),(97,false)]
theorem der_139999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139999 :=
  CNF.rup_sound cl_139999 [cl_138405,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138405 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_140000 : CNF.NClause := [(138,false),(140,false),(94,false),(110,false),(101,false),(117,false),(103,false)]
theorem der_140000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140000 :=
  CNF.rup_sound cl_140000 [cl_138407,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138407 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_140001 : CNF.NClause := [(71,true),(84,true),(13,false),(26,true),(1,true),(5,true),(24,true)]
theorem der_140001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140001 :=
  CNF.rup_sound cl_140001 [cl_138410,cl_76597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138410 v h) (hints_cons _ _ _ (der_76597 v h) (by intro d hd; cases hd)))
def cl_140002 : CNF.NClause := [(142,false),(150,false),(60,false),(119,false),(111,false),(99,false),(105,false)]
theorem der_140002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140002 :=
  CNF.rup_sound cl_140002 [cl_138411,cl_88593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138411 v h) (hints_cons _ _ _ (der_88593 v h) (by intro d hd; cases hd)))
def cl_140003 : CNF.NClause := [(128,false),(153,false),(133,false),(34,false),(96,false),(101,false),(116,false)]
theorem der_140003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140003 :=
  CNF.rup_sound cl_140003 [cl_138412,cl_115747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138412 v h) (hints_cons _ _ _ (der_115747 v h) (by intro d hd; cases hd)))
def cl_140006 : CNF.NClause := [(150,false),(130,false),(42,false),(121,false),(111,false),(100,false),(103,false)]
theorem der_140006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140006 :=
  CNF.rup_sound cl_140006 [cl_138414,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138414 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140007 : CNF.NClause := [(138,false),(140,false),(119,false),(40,false),(100,false),(113,false),(112,false)]
theorem der_140007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140007 :=
  CNF.rup_sound cl_140007 [cl_138416,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138416 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_140008 : CNF.NClause := [(145,false),(133,false),(53,false),(121,false),(117,false),(95,false),(109,false)]
theorem der_140008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140008 :=
  CNF.rup_sound cl_140008 [cl_138417,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138417 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_140009 : CNF.NClause := [(138,false),(140,false),(44,false),(119,false),(96,false),(102,false),(109,false)]
theorem der_140009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140009 :=
  CNF.rup_sound cl_140009 [cl_138418,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138418 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_140010 : CNF.NClause := [(128,false),(39,false),(126,false),(59,false),(48,false),(60,false),(40,false)]
theorem der_140010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140010 :=
  CNF.rup_sound cl_140010 [cl_138420,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138420 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_140012 : CNF.NClause := [(150,false),(95,false),(38,false),(120,false),(113,false),(104,false),(148,false)]
theorem der_140012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140012 :=
  CNF.rup_sound cl_140012 [cl_138424,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138424 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140013 : CNF.NClause := [(144,false),(129,false),(59,false),(121,false),(104,false),(112,false),(93,false)]
theorem der_140013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140013 :=
  CNF.rup_sound cl_140013 [cl_138425,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138425 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_140015 : CNF.NClause := [(138,true),(148,false),(13,false),(12,false),(143,true),(128,true),(94,true)]
theorem der_140015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140015 :=
  CNF.rup_sound cl_140015 [cl_138430,cl_80957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138430 v h) (hints_cons _ _ _ (der_80957 v h) (by intro d hd; cases hd)))
def cl_140016 : CNF.NClause := [(137,false),(136,false),(141,false),(150,false),(50,false),(99,false),(112,false)]
theorem der_140016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140016 :=
  CNF.rup_sound cl_140016 [cl_138431,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138431 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_140017 : CNF.NClause := [(142,false),(153,false),(141,false),(39,false),(150,false),(50,false),(106,false)]
theorem der_140017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140017 :=
  CNF.rup_sound cl_140017 [cl_138432,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138432 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_140019 : CNF.NClause := [(126,false),(127,false),(120,false),(47,false),(99,false),(108,false),(97,false)]
theorem der_140019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140019 :=
  CNF.rup_sound cl_140019 [cl_138436,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138436 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_140020 : CNF.NClause := [(55,true),(923,false),(63,false),(84,false),(91,false),(928,true),(906,true)]
theorem der_140020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140020 :=
  CNF.rup_sound cl_140020 [cl_138439,cl_137963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138439 v h) (hints_cons _ _ _ (der_137963 v h) (by intro d hd; cases hd)))
def cl_140021 : CNF.NClause := [(39,false),(48,false),(127,false),(50,false),(126,false),(60,false),(106,false)]
theorem der_140021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140021 :=
  CNF.rup_sound cl_140021 [cl_138440,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138440 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_140022 : CNF.NClause := [(39,false),(150,false),(130,false),(135,false),(59,false),(50,false),(53,false)]
theorem der_140022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140022 :=
  CNF.rup_sound cl_140022 [cl_138442,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138442 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_140024 : CNF.NClause := [(136,false),(121,false),(50,false),(148,false),(105,false),(102,false),(108,false)]
theorem der_140024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140024 :=
  CNF.rup_sound cl_140024 [cl_138445,cl_137960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138445 v h) (hints_cons _ _ _ (der_137960 v h) (by intro d hd; cases hd)))
def cl_140025 : CNF.NClause := [(151,false),(140,false),(50,false),(121,false),(94,false),(105,false),(102,false)]
theorem der_140025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140025 :=
  CNF.rup_sound cl_140025 [cl_138446,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138446 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_140026 : CNF.NClause := [(129,false),(134,false),(120,false),(47,false),(99,false),(108,false),(97,false)]
theorem der_140026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140026 :=
  CNF.rup_sound cl_140026 [cl_138447,cl_137961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138447 v h) (hints_cons _ _ _ (der_137961 v h) (by intro d hd; cases hd)))
def cl_140027 : CNF.NClause := [(137,false),(145,false),(50,false),(121,false),(94,false),(105,false),(108,false)]
theorem der_140027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140027 :=
  CNF.rup_sound cl_140027 [cl_138448,cl_88561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138448 v h) (hints_cons _ _ _ (der_88561 v h) (by intro d hd; cases hd)))
def cl_140030 : CNF.NClause := [(137,false),(142,false),(133,false),(150,false),(50,false),(43,false),(36,false)]
theorem der_140030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140030 :=
  CNF.rup_sound cl_140030 [cl_138451,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138451 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_140031 : CNF.NClause := [(144,false),(134,false),(122,false),(57,false),(110,false),(114,false),(93,false)]
theorem der_140031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140031 :=
  CNF.rup_sound cl_140031 [cl_138452,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138452 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_140032 : CNF.NClause := [(144,false),(134,false),(120,false),(47,false),(108,false),(97,false),(115,false)]
theorem der_140032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140032 :=
  CNF.rup_sound cl_140032 [cl_138453,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138453 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_140033 : CNF.NClause := [(142,false),(150,false),(42,false),(59,false),(45,false),(44,false),(108,false)]
theorem der_140033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140033 :=
  CNF.rup_sound cl_140033 [cl_138454,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138454 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_140034 : CNF.NClause := [(142,false),(150,false),(44,false),(119,false),(103,false),(109,false),(115,false)]
theorem der_140034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140034 :=
  CNF.rup_sound cl_140034 [cl_138455,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138455 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_140035 : CNF.NClause := [(142,false),(126,false),(150,false),(50,false),(34,false),(121,false),(94,false)]
theorem der_140035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140035 :=
  CNF.rup_sound cl_140035 [cl_138456,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138456 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_140036 : CNF.NClause := [(39,false),(129,false),(134,false),(121,false),(96,false),(99,false),(110,false)]
theorem der_140036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140036 :=
  CNF.rup_sound cl_140036 [cl_138457,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138457 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_140037 : CNF.NClause := [(142,false),(97,false),(42,false),(121,false),(114,false),(148,false),(103,false)]
theorem der_140037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140037 :=
  CNF.rup_sound cl_140037 [cl_138460,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138460 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_140038 : CNF.NClause := [(905,false),(37,true),(82,false),(66,false),(926,true),(912,true),(914,true)]
theorem der_140038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140038 :=
  CNF.rup_sound cl_140038 [cl_138461,cl_137958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138461 v h) (hints_cons _ _ _ (der_137958 v h) (by intro d hd; cases hd)))
def cl_140039 : CNF.NClause := [(55,true),(91,false),(63,false),(923,false),(928,true),(915,true),(906,true)]
theorem der_140039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140039 :=
  CNF.rup_sound cl_140039 [cl_138463,cl_137963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138463 v h) (hints_cons _ _ _ (der_137963 v h) (by intro d hd; cases hd)))
def cl_140040 : CNF.NClause := [(137,false),(121,false),(142,false),(148,false),(42,false),(141,false),(97,false)]
theorem der_140040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140040 :=
  CNF.rup_sound cl_140040 [cl_138466,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138466 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_140042 : CNF.NClause := [(128,false),(126,false),(43,false),(122,false),(116,false),(112,false),(103,false)]
theorem der_140042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140042 :=
  CNF.rup_sound cl_140042 [cl_138468,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138468 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_140043 : CNF.NClause := [(150,false),(130,false),(59,false),(121,false),(104,false),(112,false),(115,false)]
theorem der_140043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140043 :=
  CNF.rup_sound cl_140043 [cl_138469,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138469 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140044 : CNF.NClause := [(142,false),(150,false),(42,false),(53,false),(45,false),(58,false),(102,false)]
theorem der_140044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140044 :=
  CNF.rup_sound cl_140044 [cl_138470,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138470 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_140045 : CNF.NClause := [(145,false),(133,false),(42,false),(59,false),(37,false),(57,false),(94,false)]
theorem der_140045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140045 :=
  CNF.rup_sound cl_140045 [cl_138473,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138473 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_140046 : CNF.NClause := [(144,false),(134,false),(55,false),(122,false),(94,false),(111,false),(115,false)]
theorem der_140046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140046 :=
  CNF.rup_sound cl_140046 [cl_138475,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138475 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140048 : CNF.NClause := [(904,true),(52,true),(73,false),(66,false),(920,false),(926,true),(918,true)]
theorem der_140048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140048 :=
  CNF.rup_sound cl_140048 [cl_138477,cl_133089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138477 v h) (hints_cons _ _ _ (der_133089 v h) (by intro d hd; cases hd)))
def cl_140049 : CNF.NClause := [(128,false),(45,false),(137,false),(126,false),(141,false),(34,false),(32,false)]
theorem der_140049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140049 :=
  CNF.rup_sound cl_140049 [cl_138478,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138478 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_140050 : CNF.NClause := [(128,false),(126,false),(134,false),(139,false),(43,false),(122,false),(116,false)]
theorem der_140050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140050 :=
  CNF.rup_sound cl_140050 [cl_138479,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138479 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_140051 : CNF.NClause := [(136,false),(144,false),(148,false),(134,false),(60,false),(44,false),(40,false)]
theorem der_140051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140051 :=
  CNF.rup_sound cl_140051 [cl_138480,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138480 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140052 : CNF.NClause := [(130,false),(118,false),(35,false),(148,false),(99,false),(114,false),(104,false)]
theorem der_140052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140052 :=
  CNF.rup_sound cl_140052 [cl_138481,cl_139831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138481 v h) (hints_cons _ _ _ (der_139831 v h) (by intro d hd; cases hd)))
def cl_140053 : CNF.NClause := [(128,false),(144,false),(125,false),(134,false),(52,false),(48,false),(100,false)]
theorem der_140053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140053 :=
  CNF.rup_sound cl_140053 [cl_138484,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138484 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_140054 : CNF.NClause := [(128,false),(126,false),(59,false),(50,false),(52,false),(40,false),(95,false)]
theorem der_140054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140054 :=
  CNF.rup_sound cl_140054 [cl_138485,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138485 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_140055 : CNF.NClause := [(141,false),(146,false),(137,false),(39,false),(53,false),(52,false),(36,false)]
theorem der_140055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140055 :=
  CNF.rup_sound cl_140055 [cl_138488,cl_139837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138488 v h) (hints_cons _ _ _ (der_139837 v h) (by intro d hd; cases hd)))
def cl_140056 : CNF.NClause := [(39,false),(127,false),(125,false),(121,false),(99,false),(110,false),(113,false)]
theorem der_140056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140056 :=
  CNF.rup_sound cl_140056 [cl_138489,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138489 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_140057 : CNF.NClause := [(137,false),(133,false),(129,false),(32,false),(118,false),(97,false),(41,false)]
theorem der_140057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140057 :=
  CNF.rup_sound cl_140057 [cl_138490,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138490 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_140058 : CNF.NClause := [(63,true),(1057,true),(1076,true),(1077,true),(1082,true),(1071,true),(1075,true),(1060,true)]
theorem der_140058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140058 :=
  CNF.rup_sound cl_140058 [cl_138497,cl_124863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138497 v h) (hints_cons _ _ _ (der_124863 v h) (by intro d hd; cases hd)))
def cl_140059 : CNF.NClause := [(144,false),(129,false),(86,false),(44,false),(119,false),(96,false),(103,false),(109,false)]
theorem der_140059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140059 :=
  CNF.rup_sound cl_140059 [cl_138503,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138503 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_140060 : CNF.NClause := [(151,false),(144,false),(139,false),(68,false),(45,false),(94,false),(117,false),(103,false)]
theorem der_140060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140060 :=
  CNF.rup_sound cl_140060 [cl_138504,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138504 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_140061 : CNF.NClause := [(126,false),(125,false),(131,true),(49,false),(122,false),(96,false),(104,false),(108,false)]
theorem der_140061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140061 :=
  CNF.rup_sound cl_140061 [cl_138505,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138505 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_140063 : CNF.NClause := [(126,false),(125,false),(131,true),(114,false),(113,false),(116,false),(123,false),(36,false)]
theorem der_140063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140063 :=
  CNF.rup_sound cl_140063 [cl_138507,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138507 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_140064 : CNF.NClause := [(146,false),(135,false),(80,false),(55,false),(122,false),(94,false),(107,false),(115,false)]
theorem der_140064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140064 :=
  CNF.rup_sound cl_140064 [cl_138508,cl_85856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138508 v h) (hints_cons _ _ _ (der_85856 v h) (by intro d hd; cases hd)))
def cl_140065 : CNF.NClause := [(126,false),(125,false),(131,true),(104,false),(123,false),(106,false),(103,false),(41,false)]
theorem der_140065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140065 :=
  CNF.rup_sound cl_140065 [cl_138509,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138509 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_140066 : CNF.NClause := [(126,false),(127,false),(131,true),(59,false),(121,false),(104,false),(112,false),(93,false)]
theorem der_140066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140066 :=
  CNF.rup_sound cl_140066 [cl_138510,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138510 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_140067 : CNF.NClause := [(129,false),(139,false),(18,false),(49,false),(122,false),(96,false),(100,false),(104,false)]
theorem der_140067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140067 :=
  CNF.rup_sound cl_140067 [cl_138512,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138512 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_140068 : CNF.NClause := [(128,false),(134,false),(139,false),(35,false),(118,false),(94,false),(99,false),(114,false)]
theorem der_140068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140068 :=
  CNF.rup_sound cl_140068 [cl_138513,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138513 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_140069 : CNF.NClause := [(39,false),(126,false),(125,false),(131,true),(121,false),(96,false),(99,false),(113,false)]
theorem der_140069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140069 :=
  CNF.rup_sound cl_140069 [cl_138514,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138514 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_140070 : CNF.NClause := [(919,false),(914,true),(917,true),(907,true),(903,true),(911,true),(74,true),(916,true)]
theorem der_140070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140070 :=
  CNF.rup_sound cl_140070 [cl_138516,cl_124819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138516 v h) (hints_cons _ _ _ (der_124819 v h) (by intro d hd; cases hd)))
def cl_140071 : CNF.NClause := [(132,false),(152,false),(84,false),(118,false),(33,false),(100,false),(105,false),(95,false)]
theorem der_140071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140071 :=
  CNF.rup_sound cl_140071 [cl_138517,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138517 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_140072 : CNF.NClause := [(129,false),(139,false),(86,false),(37,false),(122,false),(101,false),(105,false),(97,false)]
theorem der_140072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140072 :=
  CNF.rup_sound cl_140072 [cl_138518,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138518 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_140073 : CNF.NClause := [(126,false),(127,false),(59,false),(85,false),(121,false),(104,false),(112,false),(93,false)]
theorem der_140073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140073 :=
  CNF.rup_sound cl_140073 [cl_138519,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138519 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_140074 : CNF.NClause := [(144,false),(139,false),(50,false),(79,false),(121,false),(94,false),(116,false),(105,false)]
theorem der_140074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140074 :=
  CNF.rup_sound cl_140074 [cl_138520,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138520 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_140075 : CNF.NClause := [(128,false),(144,false),(129,false),(34,false),(118,false),(111,false),(96,false),(106,false)]
theorem der_140075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140075 :=
  CNF.rup_sound cl_140075 [cl_138521,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138521 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_140076 : CNF.NClause := [(128,false),(146,false),(153,false),(24,false),(76,false),(151,true),(36,false),(115,true)]
theorem der_140076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140076 :=
  CNF.rup_sound cl_140076 [cl_107548,cl_139773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107548 v h) (hints_cons _ _ _ (der_139773 v h) (by intro d hd; cases hd)))
def cl_140077 : CNF.NClause := [(137,false),(145,false),(50,false),(121,false),(94,false),(67,false),(105,false),(108,false)]
theorem der_140077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140077 :=
  CNF.rup_sound cl_140077 [cl_138522,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138522 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_140078 : CNF.NClause := [(137,false),(145,false),(45,false),(120,false),(94,false),(67,false),(101,false),(117,false)]
theorem der_140078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140078 :=
  CNF.rup_sound cl_140078 [cl_138523,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138523 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_140079 : CNF.NClause := [(143,false),(135,false),(69,false),(49,false),(122,false),(96,false),(104,false),(117,false)]
theorem der_140079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140079 :=
  CNF.rup_sound cl_140079 [cl_138526,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138526 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_140080 : CNF.NClause := [(138,false),(128,false),(127,false),(45,false),(120,false),(110,false),(117,false),(103,false)]
theorem der_140080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140080 :=
  CNF.rup_sound cl_140080 [cl_138527,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138527 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_140081 : CNF.NClause := [(126,false),(127,false),(85,false),(43,false),(122,false),(99,false),(112,false),(103,false)]
theorem der_140081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140081 :=
  CNF.rup_sound cl_140081 [cl_138528,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138528 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_140082 : CNF.NClause := [(138,false),(128,false),(127,false),(42,false),(121,false),(100,false),(97,false),(103,false)]
theorem der_140082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140082 :=
  CNF.rup_sound cl_140082 [cl_138529,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138529 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_140083 : CNF.NClause := [(134,false),(139,false),(49,false),(73,false),(122,false),(96,false),(100,false),(117,false)]
theorem der_140083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140083 :=
  CNF.rup_sound cl_140083 [cl_138530,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138530 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_140084 : CNF.NClause := [(134,false),(139,false),(73,false),(55,false),(122,false),(94,false),(115,false),(98,false)]
theorem der_140084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140084 :=
  CNF.rup_sound cl_140084 [cl_138532,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138532 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140085 : CNF.NClause := [(138,false),(127,false),(125,false),(122,false),(57,false),(110,false),(114,false),(93,false)]
theorem der_140085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140085 :=
  CNF.rup_sound cl_140085 [cl_138534,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138534 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_140086 : CNF.NClause := [(134,false),(139,false),(50,false),(75,false),(121,false),(94,false),(116,false),(102,false)]
theorem der_140086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140086 :=
  CNF.rup_sound cl_140086 [cl_138536,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138536 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140087 : CNF.NClause := [(134,false),(139,false),(73,false),(58,false),(120,false),(100,false),(116,false),(93,false)]
theorem der_140087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140087 :=
  CNF.rup_sound cl_140087 [cl_138537,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138537 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_140088 : CNF.NClause := [(138,false),(141,false),(146,false),(88,false),(48,true),(142,true),(85,false),(74,false)]
theorem der_140088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140088 :=
  CNF.rup_sound cl_140088 [cl_138539,cl_15783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138539 v h) (hints_cons _ _ _ (der_15783 v h) (by intro d hd; cases hd)))
def cl_140089 : CNF.NClause := [(138,false),(122,false),(125,false),(55,false),(126,false),(94,false),(111,false),(98,false)]
theorem der_140089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140089 :=
  CNF.rup_sound cl_140089 [cl_138542,cl_76529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138542 v h) (hints_cons _ _ _ (der_76529 v h) (by intro d hd; cases hd)))
def cl_140090 : CNF.NClause := [(138,false),(146,false),(147,false),(90,false),(35,false),(118,false),(99,false),(104,false)]
theorem der_140090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140090 :=
  CNF.rup_sound cl_140090 [cl_109794,cl_139831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109794 v h) (hints_cons _ _ _ (der_139831 v h) (by intro d hd; cases hd)))
def cl_140091 : CNF.NClause := [(150,false),(130,false),(83,false),(35,false),(118,false),(94,false),(99,false),(104,false)]
theorem der_140091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140091 :=
  CNF.rup_sound cl_140091 [cl_138543,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138543 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140092 : CNF.NClause := [(130,false),(114,false),(80,false),(35,false),(118,false),(99,false),(148,false),(104,false)]
theorem der_140092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140092 :=
  CNF.rup_sound cl_140092 [cl_138544,cl_139831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138544 v h) (hints_cons _ _ _ (der_139831 v h) (by intro d hd; cases hd)))
def cl_140093 : CNF.NClause := [(144,false),(42,false),(121,false),(14,true),(111,false),(114,false),(97,false),(41,false)]
theorem der_140093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140093 :=
  CNF.rup_sound cl_140093 [cl_138545,cl_115964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138545 v h) (hints_cons _ _ _ (der_115964 v h) (by intro d hd; cases hd)))
def cl_140094 : CNF.NClause := [(39,false),(150,false),(130,false),(83,false),(121,false),(96,false),(99,false),(107,false)]
theorem der_140094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140094 :=
  CNF.rup_sound cl_140094 [cl_138547,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138547 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_140095 : CNF.NClause := [(138,false),(147,false),(22,false),(35,false),(118,false),(99,false),(104,false),(109,false)]
theorem der_140095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140095 :=
  CNF.rup_sound cl_140095 [cl_103271,cl_139831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103271 v h) (hints_cons _ _ _ (der_139831 v h) (by intro d hd; cases hd)))
def cl_140096 : CNF.NClause := [(145,false),(99,false),(39,false),(77,false),(121,false),(96,false),(141,false),(113,false)]
theorem der_140096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140096 :=
  CNF.rup_sound cl_140096 [cl_138553,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138553 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_140097 : CNF.NClause := [(136,false),(34,false),(63,false),(148,false),(118,false),(96,false),(101,false),(106,false)]
theorem der_140097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140097 :=
  CNF.rup_sound cl_140097 [cl_138554,cl_115747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138554 v h) (hints_cons _ _ _ (der_115747 v h) (by intro d hd; cases hd)))
def cl_140098 : CNF.NClause := [(150,false),(148,false),(83,false),(34,false),(118,false),(96,false),(101,false),(116,false)]
theorem der_140098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140098 :=
  CNF.rup_sound cl_140098 [cl_138555,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138555 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140099 : CNF.NClause := [(138,false),(145,false),(133,false),(38,false),(69,false),(111,false),(102,false),(95,false)]
theorem der_140099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140099 :=
  CNF.rup_sound cl_140099 [cl_138558,cl_129081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138558 v h) (hints_cons _ _ _ (der_129081 v h) (by intro d hd; cases hd)))
def cl_140100 : CNF.NClause := [(138,false),(34,false),(77,false),(47,false),(118,false),(111,false),(96,false),(116,false)]
theorem der_140100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140100 :=
  CNF.rup_sound cl_140100 [cl_103427,cl_139803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103427 v h) (hints_cons _ _ _ (der_139803 v h) (by intro d hd; cases hd)))
def cl_140101 : CNF.NClause := [(129,false),(134,false),(42,false),(50,false),(38,false),(53,false),(82,false),(107,false)]
theorem der_140101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140101 :=
  CNF.rup_sound cl_140101 [cl_138559,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138559 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_140102 : CNF.NClause := [(39,false),(129,false),(143,false),(134,false),(49,false),(83,false),(122,false),(100,false)]
theorem der_140102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140102 :=
  CNF.rup_sound cl_140102 [cl_138560,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138560 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_140103 : CNF.NClause := [(144,false),(134,false),(50,false),(43,false),(49,false),(75,false),(57,false),(107,false)]
theorem der_140103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140103 :=
  CNF.rup_sound cl_140103 [cl_138562,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138562 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140104 : CNF.NClause := [(145,false),(133,false),(59,false),(50,false),(63,false),(54,false),(47,false),(110,false)]
theorem der_140104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140104 :=
  CNF.rup_sound cl_140104 [cl_138563,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138563 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_140105 : CNF.NClause := [(144,false),(134,false),(45,false),(75,false),(120,false),(94,false),(110,false),(117,false)]
theorem der_140105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140105 :=
  CNF.rup_sound cl_140105 [cl_138566,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138566 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140107 : CNF.NClause := [(141,false),(133,false),(39,false),(42,false),(38,false),(45,false),(77,false),(47,false)]
theorem der_140107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140107 :=
  CNF.rup_sound cl_140107 [cl_138571,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138571 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_140109 : CNF.NClause := [(138,false),(151,false),(144,false),(134,false),(50,false),(75,false),(121,false),(108,false)]
theorem der_140109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140109 :=
  CNF.rup_sound cl_140109 [cl_138574,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138574 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140110 : CNF.NClause := [(144,false),(134,false),(74,false),(118,false),(33,false),(110,false),(95,false),(115,false)]
theorem der_140110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140110 :=
  CNF.rup_sound cl_140110 [cl_138575,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138575 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_140111 : CNF.NClause := [(150,false),(101,false),(79,false),(34,false),(118,false),(96,false),(148,false),(116,false)]
theorem der_140111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140111 :=
  CNF.rup_sound cl_140111 [cl_138576,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138576 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_140112 : CNF.NClause := [(142,false),(150,false),(83,false),(35,false),(118,false),(94,false),(99,false),(109,false)]
theorem der_140112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140112 :=
  CNF.rup_sound cl_140112 [cl_138579,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138579 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140113 : CNF.NClause := [(141,false),(133,false),(39,false),(42,false),(50,false),(38,false),(45,false),(77,false)]
theorem der_140113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140113 :=
  CNF.rup_sound cl_140113 [cl_138584,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138584 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_140114 : CNF.NClause := [(129,false),(134,false),(59,false),(82,false),(121,false),(101,false),(112,false),(93,false)]
theorem der_140114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140114 :=
  CNF.rup_sound cl_140114 [cl_138589,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138589 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_140116 : CNF.NClause := [(142,false),(145,false),(133,false),(130,false),(50,false),(82,false),(121,false),(102,false)]
theorem der_140116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140116 :=
  CNF.rup_sound cl_140116 [cl_138590,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138590 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_140118 : CNF.NClause := [(145,false),(133,false),(49,false),(82,false),(122,false),(96,false),(117,false),(108,false)]
theorem der_140118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140118 :=
  CNF.rup_sound cl_140118 [cl_138593,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138593 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_140120 : CNF.NClause := [(136,false),(38,false),(59,false),(50,false),(148,false),(45,false),(84,false),(47,false)]
theorem der_140120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140120 :=
  CNF.rup_sound cl_140120 [cl_138595,cl_137960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138595 v h) (hints_cons _ _ _ (der_137960 v h) (by intro d hd; cases hd)))
def cl_140121 : CNF.NClause := [(147,false),(131,false),(35,false),(65,false),(118,false),(94,false),(99,false),(109,false)]
theorem der_140121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140121 :=
  CNF.rup_sound cl_140121 [cl_138596,cl_88565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138596 v h) (hints_cons _ _ _ (der_88565 v h) (by intro d hd; cases hd)))
def cl_140124 : CNF.NClause := [(153,false),(145,false),(39,false),(130,false),(148,false),(143,false),(152,false),(135,true)]
theorem der_140124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140124 :=
  CNF.rup_sound cl_140124 [cl_138599,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138599 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_140125 : CNF.NClause := [(153,false),(133,false),(82,false),(122,false),(57,false),(110,false),(114,false),(102,false)]
theorem der_140125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140125 :=
  CNF.rup_sound cl_140125 [cl_138600,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138600 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_140126 : CNF.NClause := [(144,false),(134,false),(59,false),(74,false),(121,false),(112,false),(93,false),(115,false)]
theorem der_140126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140126 :=
  CNF.rup_sound cl_140126 [cl_138601,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138601 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_140127 : CNF.NClause := [(144,false),(39,false),(134,false),(74,false),(119,false),(94,false),(40,false),(112,false)]
theorem der_140127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140127 :=
  CNF.rup_sound cl_140127 [cl_138602,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138602 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_140128 : CNF.NClause := [(137,false),(129,false),(134,false),(143,true),(147,true),(130,true),(126,true),(115,true)]
theorem der_140128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140128 :=
  CNF.rup_sound cl_140128 [cl_138604,cl_137961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138604 v h) (hints_cons _ _ _ (der_137961 v h) (by intro d hd; cases hd)))
def cl_140132 : CNF.NClause := [(144,false),(134,false),(53,false),(75,false),(121,false),(117,false),(95,false),(109,false)]
theorem der_140132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140132 :=
  CNF.rup_sound cl_140132 [cl_138612,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138612 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140133 : CNF.NClause := [(138,false),(141,false),(127,false),(85,false),(48,false),(136,true),(146,true),(101,true)]
theorem der_140133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140133 :=
  CNF.rup_sound cl_140133 [cl_138613,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138613 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_140135 : CNF.NClause := [(127,false),(125,false),(71,false),(70,false),(80,false),(76,false),(75,false),(118,true)]
theorem der_140135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140135 :=
  CNF.rup_sound cl_140135 [cl_138619,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138619 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_140136 : CNF.NClause := [(137,false),(145,false),(39,false),(130,false),(152,false),(12,false),(64,false),(57,false)]
theorem der_140136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140136 :=
  CNF.rup_sound cl_140136 [cl_138620,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138620 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_140137 : CNF.NClause := [(141,false),(39,false),(150,false),(148,false),(50,false),(152,true),(53,false),(151,true)]
theorem der_140137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140137 :=
  CNF.rup_sound cl_140137 [cl_138621,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138621 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_140139 : CNF.NClause := [(141,false),(133,false),(59,false),(53,false),(77,false),(54,false),(47,false),(107,false)]
theorem der_140139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140139 :=
  CNF.rup_sound cl_140139 [cl_138623,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138623 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_140140 : CNF.NClause := [(129,false),(143,false),(134,false),(135,false),(82,false),(60,false),(44,false),(113,false)]
theorem der_140140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140140 :=
  CNF.rup_sound cl_140140 [cl_138625,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138625 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_140141 : CNF.NClause := [(151,false),(137,false),(136,false),(133,false),(148,false),(53,false),(121,false),(117,false)]
theorem der_140141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140141 :=
  CNF.rup_sound cl_140141 [cl_138626,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138626 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_140142 : CNF.NClause := [(150,false),(130,false),(71,false),(58,false),(120,false),(100,false),(116,false),(107,false)]
theorem der_140142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140142 :=
  CNF.rup_sound cl_140142 [cl_138627,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138627 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140143 : CNF.NClause := [(142,false),(150,false),(71,false),(58,false),(120,false),(116,false),(107,false),(109,false)]
theorem der_140143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140143 :=
  CNF.rup_sound cl_140143 [cl_138628,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138628 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140146 : CNF.NClause := [(138,false),(131,false),(141,true),(88,false),(140,true),(142,true),(85,false),(84,false)]
theorem der_140146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140146 :=
  CNF.rup_sound cl_140146 [cl_138631,cl_101685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138631 v h) (hints_cons _ _ _ (der_101685 v h) (by intro d hd; cases hd)))
def cl_140147 : CNF.NClause := [(150,false),(130,false),(71,false),(48,false),(119,false),(107,false),(108,false),(95,false)]
theorem der_140147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140147 :=
  CNF.rup_sound cl_140147 [cl_138634,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138634 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140149 : CNF.NClause := [(144,false),(129,false),(83,false),(48,false),(119,false),(107,false),(108,false),(95,false)]
theorem der_140149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140149 :=
  CNF.rup_sound cl_140149 [cl_138636,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138636 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_140150 : CNF.NClause := [(39,false),(130,false),(148,false),(42,false),(59,false),(53,false),(84,false),(54,false)]
theorem der_140150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140150 :=
  CNF.rup_sound cl_140150 [cl_138638,cl_137960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138638 v h) (hints_cons _ _ _ (der_137960 v h) (by intro d hd; cases hd)))
def cl_140151 : CNF.NClause := [(916,false),(914,true),(12,false),(70,false),(76,false),(48,true),(917,true),(918,true)]
theorem der_140151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140151 :=
  CNF.rup_sound cl_140151 [cl_138641,cl_137956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138641 v h) (hints_cons _ _ _ (der_137956 v h) (by intro d hd; cases hd)))
def cl_140152 : CNF.NClause := [(144,false),(134,false),(42,false),(43,false),(53,false),(48,false),(74,false),(102,false)]
theorem der_140152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140152 :=
  CNF.rup_sound cl_140152 [cl_138642,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138642 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_140153 : CNF.NClause := [(138,false),(144,false),(140,false),(129,false),(42,false),(84,false),(121,false),(111,false)]
theorem der_140153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140153 :=
  CNF.rup_sound cl_140153 [cl_138643,cl_56322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138643 v h) (hints_cons _ _ _ (der_56322 v h) (by intro d hd; cases hd)))
def cl_140154 : CNF.NClause := [(144,false),(134,false),(73,false),(52,false),(48,false),(60,false),(44,false),(100,false)]
theorem der_140154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140154 :=
  CNF.rup_sound cl_140154 [cl_138644,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138644 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_140155 : CNF.NClause := [(144,false),(129,false),(68,false),(53,false),(121,false),(106,false),(95,false),(109,false)]
theorem der_140155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140155 :=
  CNF.rup_sound cl_140155 [cl_138645,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138645 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_140156 : CNF.NClause := [(129,false),(134,false),(42,false),(82,false),(121,false),(111,false),(100,false),(97,false)]
theorem der_140156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140156 :=
  CNF.rup_sound cl_140156 [cl_138648,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138648 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_140158 : CNF.NClause := [(129,false),(134,false),(42,false),(43,false),(38,false),(53,false),(82,false),(47,false)]
theorem der_140158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140158 :=
  CNF.rup_sound cl_140158 [cl_138650,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138650 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_140159 : CNF.NClause := [(142,false),(130,false),(152,false),(42,false),(90,false),(153,true),(54,false),(47,false)]
theorem der_140159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140159 :=
  CNF.rup_sound cl_140159 [cl_127848,cl_139820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127848 v h) (hints_cons _ _ _ (der_139820 v h) (by intro d hd; cases hd)))
def cl_140160 : CNF.NClause := [(146,false),(39,false),(125,false),(42,false),(59,false),(84,false),(33,false),(102,false)]
theorem der_140160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140160 :=
  CNF.rup_sound cl_140160 [cl_138660,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138660 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_140163 : CNF.NClause := [(129,false),(134,false),(42,false),(49,false),(82,false),(37,false),(58,false),(106,false)]
theorem der_140163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140163 :=
  CNF.rup_sound cl_140163 [cl_138663,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138663 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_140164 : CNF.NClause := [(150,false),(134,false),(90,false),(131,true),(60,false),(137,true),(125,true),(105,true)]
theorem der_140164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140164 :=
  CNF.rup_sound cl_140164 [cl_138665,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138665 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_140165 : CNF.NClause := [(151,false),(147,false),(150,false),(148,false),(50,false),(83,false),(34,false),(33,false)]
theorem der_140165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140165 :=
  CNF.rup_sound cl_140165 [cl_138666,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138666 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_140166 : CNF.NClause := [(150,false),(121,false),(80,false),(50,false),(55,false),(116,false),(105,false),(108,false)]
theorem der_140166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140166 :=
  CNF.rup_sound cl_140166 [cl_138667,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138667 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_140167 : CNF.NClause := [(141,false),(133,false),(49,false),(77,false),(122,false),(96,false),(104,false),(117,false)]
theorem der_140167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140167 :=
  CNF.rup_sound cl_140167 [cl_138670,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138670 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_140168 : CNF.NClause := [(141,false),(133,false),(77,false),(55,false),(122,false),(111,false),(115,false),(98,false)]
theorem der_140168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140168 :=
  CNF.rup_sound cl_140168 [cl_138671,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138671 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_140169 : CNF.NClause := [(128,false),(153,false),(133,false),(49,false),(48,false),(76,false),(44,false),(118,false)]
theorem der_140169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140169 :=
  CNF.rup_sound cl_140169 [cl_138674,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138674 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_140170 : CNF.NClause := [(37,false),(133,false),(127,false),(126,false),(64,false),(122,false),(44,false),(97,false)]
theorem der_140170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140170 :=
  CNF.rup_sound cl_140170 [cl_138675,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138675 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_140171 : CNF.NClause := [(153,false),(145,false),(144,false),(152,false),(139,false),(53,false),(63,false),(19,false)]
theorem der_140171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140171 :=
  CNF.rup_sound cl_140171 [cl_136350,cl_139776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136350 v h) (hints_cons _ _ _ (der_139776 v h) (by intro d hd; cases hd)))
def cl_140172 : CNF.NClause := [(130,false),(139,false),(88,false),(21,false),(59,false),(140,true),(143,true),(101,true)]
theorem der_140172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140172 :=
  CNF.rup_sound cl_140172 [cl_136371,cl_139840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136371 v h) (hints_cons _ _ _ (der_139840 v h) (by intro d hd; cases hd)))
def cl_140175 : CNF.NClause := [(128,false),(126,false),(131,true),(74,false),(60,false),(119,false),(111,false),(117,false),(93,false)]
theorem der_140175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140175 :=
  CNF.rup_sound cl_140175 [cl_138690,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138690 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_140176 : CNF.NClause := [(144,false),(129,false),(83,false),(48,false),(84,false),(119,false),(107,false),(108,false),(95,false)]
theorem der_140176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140176 :=
  CNF.rup_sound cl_140176 [cl_138691,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138691 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_140177 : CNF.NClause := [(151,false),(140,false),(141,true),(75,false),(55,false),(122,false),(94,false),(111,false),(98,false)]
theorem der_140177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140177 :=
  CNF.rup_sound cl_140177 [cl_138692,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138692 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_140178 : CNF.NClause := [(71,true),(1057,true),(1073,true),(1076,true),(1082,true),(1066,true),(1068,true),(1060,true),(1056,false)]
theorem der_140178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140178 :=
  CNF.rup_sound cl_140178 [cl_138694,cl_125313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138694 v h) (hints_cons _ _ _ (der_125313 v h) (by intro d hd; cases hd)))
def cl_140179 : CNF.NClause := [(144,false),(129,false),(38,false),(86,false),(83,false),(120,false),(111,false),(104,false),(95,false)]
theorem der_140179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140179 :=
  CNF.rup_sound cl_140179 [cl_138696,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138696 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_140180 : CNF.NClause := [(147,false),(125,false),(89,false),(142,true),(132,true),(86,false),(137,true),(65,false),(112,true)]
theorem der_140180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140180 :=
  CNF.rup_sound cl_140180 [cl_138697,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138697 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_140181 : CNF.NClause := [(144,false),(129,false),(59,false),(71,false),(86,false),(121,false),(104,false),(112,false),(93,false)]
theorem der_140181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140181 :=
  CNF.rup_sound cl_140181 [cl_138699,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138699 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_140182 : CNF.NClause := [(129,false),(139,false),(86,false),(78,false),(35,false),(118,false),(94,false),(99,false),(104,false)]
theorem der_140182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140182 :=
  CNF.rup_sound cl_140182 [cl_138700,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138700 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_140183 : CNF.NClause := [(144,false),(39,false),(129,false),(42,false),(68,false),(59,false),(38,false),(83,false),(98,false)]
theorem der_140183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140183 :=
  CNF.rup_sound cl_140183 [cl_138701,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138701 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_140184 : CNF.NClause := [(127,false),(125,false),(70,false),(46,false),(75,false),(110,false),(123,false),(108,false),(109,false)]
theorem der_140184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140184 :=
  CNF.rup_sound cl_140184 [cl_138702,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138702 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_140185 : CNF.NClause := [(126,false),(127,false),(85,false),(75,false),(104,false),(107,false),(123,false),(103,false),(41,false)]
theorem der_140185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140185 :=
  CNF.rup_sound cl_140185 [cl_138703,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138703 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_140186 : CNF.NClause := [(143,false),(152,false),(141,true),(142,true),(58,false),(120,false),(100,false),(107,false),(109,false)]
theorem der_140186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140186 :=
  CNF.rup_sound cl_140186 [cl_138705,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138705 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_140187 : CNF.NClause := [(142,false),(136,false),(77,false),(60,false),(64,false),(119,false),(111,false),(105,false),(93,false)]
theorem der_140187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140187 :=
  CNF.rup_sound cl_140187 [cl_138706,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138706 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_140188 : CNF.NClause := [(136,false),(130,false),(59,false),(64,false),(121,false),(72,false),(104,false),(93,false),(115,false)]
theorem der_140188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140188 :=
  CNF.rup_sound cl_140188 [cl_138707,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138707 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_140189 : CNF.NClause := [(147,false),(144,false),(129,false),(89,false),(38,false),(86,false),(111,false),(104,false),(95,false)]
theorem der_140189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140189 :=
  CNF.rup_sound cl_140189 [cl_138708,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138708 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_140190 : CNF.NClause := [(136,false),(150,false),(141,true),(152,true),(46,false),(111,false),(123,false),(108,false),(109,false)]
theorem der_140190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140190 :=
  CNF.rup_sound cl_140190 [cl_138710,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138710 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_140192 : CNF.NClause := [(137,false),(153,false),(39,false),(89,false),(152,true),(150,true),(121,false),(110,false),(113,false)]
theorem der_140192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140192 :=
  CNF.rup_sound cl_140192 [cl_138714,cl_62562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138714 v h) (hints_cons _ _ _ (der_62562 v h) (by intro d hd; cases hd)))
def cl_140193 : CNF.NClause := [(136,false),(95,false),(59,false),(50,false),(45,false),(63,false),(47,false),(67,false),(148,false)]
theorem der_140193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140193 :=
  CNF.rup_sound cl_140193 [cl_138715,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138715 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_140194 : CNF.NClause := [(126,false),(127,false),(85,false),(60,false),(75,false),(119,false),(99,false),(117,false),(93,false)]
theorem der_140194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140194 :=
  CNF.rup_sound cl_140194 [cl_138716,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138716 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_140195 : CNF.NClause := [(138,false),(140,false),(68,false),(85,false),(38,true),(77,false),(45,true),(76,false),(84,false)]
theorem der_140195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140195 :=
  CNF.rup_sound cl_140195 [cl_138717,cl_56322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138717 v h) (hints_cons _ _ _ (der_56322 v h) (by intro d hd; cases hd)))
def cl_140196 : CNF.NClause := [(151,false),(131,false),(82,false),(73,false),(34,false),(118,false),(96,false),(101,false),(106,false)]
theorem der_140196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140196 :=
  CNF.rup_sound cl_140196 [cl_138722,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138722 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_140197 : CNF.NClause := [(146,false),(153,false),(145,false),(126,false),(125,false),(53,false),(35,false),(81,false),(116,false)]
theorem der_140197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140197 :=
  CNF.rup_sound cl_140197 [cl_138723,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138723 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_140198 : CNF.NClause := [(146,false),(145,false),(141,true),(89,false),(29,false),(142,true),(71,false),(143,true),(84,false)]
theorem der_140198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140198 :=
  CNF.rup_sound cl_140198 [cl_138724,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138724 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_140200 : CNF.NClause := [(126,false),(125,false),(131,true),(120,false),(44,false),(47,false),(99,false),(108,false),(106,false)]
theorem der_140200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140200 :=
  CNF.rup_sound cl_140200 [cl_138727,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138727 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_140201 : CNF.NClause := [(128,false),(129,false),(134,false),(82,false),(35,false),(118,false),(94,false),(99,false),(109,false)]
theorem der_140201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140201 :=
  CNF.rup_sound cl_140201 [cl_138728,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138728 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_140202 : CNF.NClause := [(137,false),(118,false),(78,false),(35,false),(65,false),(141,false),(94,false),(99,false),(104,false)]
theorem der_140202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140202 :=
  CNF.rup_sound cl_140202 [cl_138730,cl_61980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138730 v h) (hints_cons _ _ _ (der_61980 v h) (by intro d hd; cases hd)))
def cl_140203 : CNF.NClause := [(144,false),(134,false),(38,false),(73,false),(120,false),(111,false),(72,false),(113,false),(95,false)]
theorem der_140203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140203 :=
  CNF.rup_sound cl_140203 [cl_138731,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138731 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_140204 : CNF.NClause := [(127,false),(125,false),(50,false),(70,false),(75,false),(121,false),(94,false),(105,false),(108,false)]
theorem der_140204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140204 :=
  CNF.rup_sound cl_140204 [cl_138732,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138732 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_140206 : CNF.NClause := [(148,false),(126,false),(152,true),(143,true),(55,true),(63,false),(151,true),(147,true),(134,true)]
theorem der_140206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140206 :=
  CNF.rup_sound cl_140206 [cl_138734,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138734 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_140207 : CNF.NClause := [(128,false),(39,false),(126,false),(148,false),(143,false),(49,false),(151,true),(129,true),(145,true)]
theorem der_140207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140207 :=
  CNF.rup_sound cl_140207 [cl_138735,cl_110533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138735 v h) (hints_cons _ _ _ (der_110533 v h) (by intro d hd; cases hd)))
def cl_140208 : CNF.NClause := [(143,false),(133,false),(131,true),(140,true),(150,true),(135,true),(40,true),(130,true),(144,true)]
theorem der_140208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140208 :=
  CNF.rup_sound cl_140208 [cl_138737,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138737 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_140209 : CNF.NClause := [(138,false),(140,false),(42,false),(68,false),(84,false),(121,false),(111,false),(114,false),(100,false)]
theorem der_140209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140209 :=
  CNF.rup_sound cl_140209 [cl_138739,cl_56322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138739 v h) (hints_cons _ _ _ (der_56322 v h) (by intro d hd; cases hd)))
def cl_140210 : CNF.NClause := [(145,false),(141,true),(89,false),(9,false),(142,true),(71,false),(143,true),(86,false),(84,false)]
theorem der_140210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140210 :=
  CNF.rup_sound cl_140210 [cl_138742,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138742 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_140211 : CNF.NClause := [(141,false),(133,false),(139,true),(45,false),(70,false),(120,false),(110,false),(117,false),(103,false)]
theorem der_140211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140211 :=
  CNF.rup_sound cl_140211 [cl_138743,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138743 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_140212 : CNF.NClause := [(150,false),(49,false),(73,false),(60,false),(65,false),(119,false),(111,false),(99,false),(105,false)]
theorem der_140212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140212 :=
  CNF.rup_sound cl_140212 [cl_138745,cl_88593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138745 v h) (hints_cons _ _ _ (der_88593 v h) (by intro d hd; cases hd)))
def cl_140214 : CNF.NClause := [(144,false),(129,false),(43,false),(71,false),(70,false),(122,false),(95,false),(112,false),(103,false)]
theorem der_140214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140214 :=
  CNF.rup_sound cl_140214 [cl_138748,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138748 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_140215 : CNF.NClause := [(137,false),(153,false),(71,false),(45,false),(120,false),(65,false),(94,false),(110,false),(101,false)]
theorem der_140215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140215 :=
  CNF.rup_sound cl_140215 [cl_138751,cl_61980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138751 v h) (hints_cons _ _ _ (der_61980 v h) (by intro d hd; cases hd)))
def cl_140217 : CNF.NClause := [(142,false),(150,false),(38,false),(71,false),(83,false),(120,false),(111,false),(113,false),(95,false)]
theorem der_140217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140217 :=
  CNF.rup_sound cl_140217 [cl_138755,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138755 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_140218 : CNF.NClause := [(144,false),(39,false),(134,false),(75,false),(119,false),(94,false),(40,false),(72,false),(112,false)]
theorem der_140218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140218 :=
  CNF.rup_sound cl_140218 [cl_138756,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138756 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_140219 : CNF.NClause := [(136,false),(130,false),(68,false),(85,false),(58,false),(120,false),(100,false),(107,false),(93,false)]
theorem der_140219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140219 :=
  CNF.rup_sound cl_140219 [cl_138757,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138757 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_140221 : CNF.NClause := [(147,false),(131,false),(125,false),(79,false),(84,false),(55,false),(122,false),(94,false),(33,false)]
theorem der_140221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140221 :=
  CNF.rup_sound cl_140221 [cl_138761,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138761 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_140226 : CNF.NClause := [(145,false),(133,false),(39,false),(143,false),(89,false),(16,false),(84,false),(96,false),(107,false)]
theorem der_140226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140226 :=
  CNF.rup_sound cl_140226 [cl_138771,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138771 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_140227 : CNF.NClause := [(98,false),(141,false),(86,false),(60,false),(120,false),(54,false),(96,false),(112,false),(68,false)]
theorem der_140227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140227 :=
  CNF.rup_sound cl_140227 [cl_138772,cl_139768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138772 v h) (hints_cons _ _ _ (der_139768 v h) (by intro d hd; cases hd)))
def cl_140228 : CNF.NClause := [(137,false),(136,false),(133,false),(150,false),(89,false),(152,true),(58,false),(120,false),(107,false)]
theorem der_140228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140228 :=
  CNF.rup_sound cl_140228 [cl_138773,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138773 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_140229 : CNF.NClause := [(131,false),(130,false),(148,false),(143,true),(133,true),(128,true),(44,false),(119,false),(96,false)]
theorem der_140229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_140229 :=
  CNF.rup_sound cl_140229 [cl_138774,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_138774 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def chunk184 : List CNF.NClause := [cl_139127,cl_139129,cl_139130,cl_139134,cl_139139,cl_139140,cl_139142,cl_139143,cl_139144,cl_139145,cl_139148,cl_139149,cl_139152,cl_139153,cl_139154,cl_139155,cl_139156,cl_139157,cl_139158,cl_139160,cl_139161,cl_139162,cl_139164,cl_139165,cl_139167,cl_139169,cl_139173,cl_139176,cl_139179,cl_139180,cl_139183,cl_139189,cl_139192,cl_139196,cl_139197,cl_139198,cl_139211,cl_139214,cl_139237,cl_139241,cl_139244,cl_139248,cl_139249,cl_139261,cl_139266,cl_139267,cl_139268,cl_139269,cl_139275,cl_139277,cl_139279,cl_139280,cl_139282,cl_139288,cl_139293,cl_139297,cl_139305,cl_139310,cl_139314,cl_139318,cl_139319,cl_139322,cl_139326,cl_139327,cl_139333,cl_139334,cl_139337,cl_139338,cl_139339,cl_139341,cl_139352,cl_139354,cl_139358,cl_139362,cl_139363,cl_139366,cl_139371,cl_139374,cl_139377,cl_139388,cl_139391,cl_139396,cl_139399,cl_139404,cl_139405,cl_139407,cl_139416,cl_139425,cl_139426,cl_139427,cl_139434,cl_139435,cl_139440,cl_139456,cl_139457,cl_139458,cl_139461,cl_139468,cl_139508,cl_139514,cl_139516,cl_139539,cl_139559,cl_139560,cl_139561,cl_139579,cl_139586,cl_139619,cl_139686,cl_139704,cl_139751,cl_139768,cl_139769,cl_139770,cl_139771,cl_139772,cl_139773,cl_139774,cl_139775,cl_139776,cl_139777,cl_139778,cl_139779,cl_139780,cl_139781,cl_139782,cl_139783,cl_139784,cl_139785,cl_139786,cl_139787,cl_139788,cl_139789,cl_139790,cl_139791,cl_139792,cl_139793,cl_139794,cl_139795,cl_139796,cl_139797,cl_139798,cl_139799,cl_139800,cl_139801,cl_139802,cl_139803,cl_139804,cl_139805,cl_139806,cl_139807,cl_139808,cl_139809,cl_139810,cl_139811,cl_139812,cl_139813,cl_139814,cl_139815,cl_139816,cl_139817,cl_139819,cl_139820,cl_139821,cl_139823,cl_139824,cl_139825,cl_139827,cl_139828,cl_139830,cl_139831,cl_139833,cl_139834,cl_139836,cl_139837,cl_139838,cl_139839,cl_139840,cl_139841,cl_139842,cl_139843,cl_139844,cl_139845,cl_139846,cl_139847,cl_139848,cl_139849,cl_139851,cl_139852,cl_139853,cl_139854,cl_139855,cl_139856,cl_139857,cl_139858,cl_139859,cl_139860,cl_139862,cl_139863,cl_139865,cl_139866,cl_139867,cl_139868,cl_139869,cl_139870,cl_139872,cl_139873,cl_139874,cl_139875,cl_139876,cl_139877,cl_139878,cl_139879,cl_139880,cl_139881,cl_139882,cl_139884,cl_139888,cl_139891,cl_139893,cl_139894,cl_139895,cl_139896,cl_139897,cl_139898,cl_139899,cl_139900,cl_139901,cl_139902,cl_139904,cl_139905,cl_139906,cl_139907,cl_139908,cl_139910,cl_139911,cl_139913,cl_139914,cl_139915,cl_139917,cl_139919,cl_139920,cl_139921,cl_139922,cl_139924,cl_139925,cl_139926,cl_139927,cl_139928,cl_139931,cl_139932,cl_139933,cl_139934,cl_139935,cl_139936,cl_139938,cl_139939,cl_139940,cl_139941,cl_139942,cl_139943,cl_139944,cl_139945,cl_139946,cl_139947,cl_139948,cl_139949,cl_139950,cl_139951,cl_139954,cl_139955,cl_139956,cl_139957,cl_139959,cl_139960,cl_139961,cl_139962,cl_139963,cl_139964,cl_139965,cl_139966,cl_139968,cl_139969,cl_139970,cl_139971,cl_139972,cl_139973,cl_139974,cl_139975,cl_139976,cl_139977,cl_139978,cl_139979,cl_139980,cl_139981,cl_139982,cl_139983,cl_139984,cl_139985,cl_139986,cl_139987,cl_139988,cl_139989,cl_139991,cl_139993,cl_139994,cl_139995,cl_139996,cl_139997,cl_139998,cl_139999,cl_140000,cl_140001,cl_140002,cl_140003,cl_140006,cl_140007,cl_140008,cl_140009,cl_140010,cl_140012,cl_140013,cl_140015,cl_140016,cl_140017,cl_140019,cl_140020,cl_140021,cl_140022,cl_140024,cl_140025,cl_140026,cl_140027,cl_140030,cl_140031,cl_140032,cl_140033,cl_140034,cl_140035,cl_140036,cl_140037,cl_140038,cl_140039,cl_140040,cl_140042,cl_140043,cl_140044,cl_140045,cl_140046,cl_140048,cl_140049,cl_140050,cl_140051,cl_140052,cl_140053,cl_140054,cl_140055,cl_140056,cl_140057,cl_140058,cl_140059,cl_140060,cl_140061,cl_140063,cl_140064,cl_140065,cl_140066,cl_140067,cl_140068,cl_140069,cl_140070,cl_140071,cl_140072,cl_140073,cl_140074,cl_140075,cl_140076,cl_140077,cl_140078,cl_140079,cl_140080,cl_140081,cl_140082,cl_140083,cl_140084,cl_140085,cl_140086,cl_140087,cl_140088,cl_140089,cl_140090,cl_140091,cl_140092,cl_140093,cl_140094,cl_140095,cl_140096,cl_140097,cl_140098,cl_140099,cl_140100,cl_140101,cl_140102,cl_140103,cl_140104,cl_140105,cl_140107,cl_140109,cl_140110,cl_140111,cl_140112,cl_140113,cl_140114,cl_140116,cl_140118,cl_140120,cl_140121,cl_140124,cl_140125,cl_140126,cl_140127,cl_140128,cl_140132,cl_140133,cl_140135,cl_140136,cl_140137,cl_140139,cl_140140,cl_140141,cl_140142,cl_140143,cl_140146,cl_140147,cl_140149,cl_140150,cl_140151,cl_140152,cl_140153,cl_140154,cl_140155,cl_140156,cl_140158,cl_140159,cl_140160,cl_140163,cl_140164,cl_140165,cl_140166,cl_140167,cl_140168,cl_140169,cl_140170,cl_140171,cl_140172,cl_140175,cl_140176,cl_140177,cl_140178,cl_140179,cl_140180,cl_140181,cl_140182,cl_140183,cl_140184,cl_140185,cl_140186,cl_140187,cl_140188,cl_140189,cl_140190,cl_140192,cl_140193,cl_140194,cl_140195,cl_140196,cl_140197,cl_140198,cl_140200,cl_140201,cl_140202,cl_140203,cl_140204,cl_140206,cl_140207,cl_140208,cl_140209,cl_140210,cl_140211,cl_140212,cl_140214,cl_140215,cl_140217,cl_140218,cl_140219,cl_140221,cl_140226,cl_140227,cl_140228,cl_140229]
theorem chunk_sound184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk184, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_139127 v h) (hints_cons _ _ _ (der_139129 v h) (hints_cons _ _ _ (der_139130 v h) (hints_cons _ _ _ (der_139134 v h) (hints_cons _ _ _ (der_139139 v h) (hints_cons _ _ _ (der_139140 v h) (hints_cons _ _ _ (der_139142 v h) (hints_cons _ _ _ (der_139143 v h) (hints_cons _ _ _ (der_139144 v h) (hints_cons _ _ _ (der_139145 v h) (hints_cons _ _ _ (der_139148 v h) (hints_cons _ _ _ (der_139149 v h) (hints_cons _ _ _ (der_139152 v h) (hints_cons _ _ _ (der_139153 v h) (hints_cons _ _ _ (der_139154 v h) (hints_cons _ _ _ (der_139155 v h) (hints_cons _ _ _ (der_139156 v h) (hints_cons _ _ _ (der_139157 v h) (hints_cons _ _ _ (der_139158 v h) (hints_cons _ _ _ (der_139160 v h) (hints_cons _ _ _ (der_139161 v h) (hints_cons _ _ _ (der_139162 v h) (hints_cons _ _ _ (der_139164 v h) (hints_cons _ _ _ (der_139165 v h) (hints_cons _ _ _ (der_139167 v h) (hints_cons _ _ _ (der_139169 v h) (hints_cons _ _ _ (der_139173 v h) (hints_cons _ _ _ (der_139176 v h) (hints_cons _ _ _ (der_139179 v h) (hints_cons _ _ _ (der_139180 v h) (hints_cons _ _ _ (der_139183 v h) (hints_cons _ _ _ (der_139189 v h) (hints_cons _ _ _ (der_139192 v h) (hints_cons _ _ _ (der_139196 v h) (hints_cons _ _ _ (der_139197 v h) (hints_cons _ _ _ (der_139198 v h) (hints_cons _ _ _ (der_139211 v h) (hints_cons _ _ _ (der_139214 v h) (hints_cons _ _ _ (der_139237 v h) (hints_cons _ _ _ (der_139241 v h) (hints_cons _ _ _ (der_139244 v h) (hints_cons _ _ _ (der_139248 v h) (hints_cons _ _ _ (der_139249 v h) (hints_cons _ _ _ (der_139261 v h) (hints_cons _ _ _ (der_139266 v h) (hints_cons _ _ _ (der_139267 v h) (hints_cons _ _ _ (der_139268 v h) (hints_cons _ _ _ (der_139269 v h) (hints_cons _ _ _ (der_139275 v h) (hints_cons _ _ _ (der_139277 v h) (hints_cons _ _ _ (der_139279 v h) (hints_cons _ _ _ (der_139280 v h) (hints_cons _ _ _ (der_139282 v h) (hints_cons _ _ _ (der_139288 v h) (hints_cons _ _ _ (der_139293 v h) (hints_cons _ _ _ (der_139297 v h) (hints_cons _ _ _ (der_139305 v h) (hints_cons _ _ _ (der_139310 v h) (hints_cons _ _ _ (der_139314 v h) (hints_cons _ _ _ (der_139318 v h) (hints_cons _ _ _ (der_139319 v h) (hints_cons _ _ _ (der_139322 v h) (hints_cons _ _ _ (der_139326 v h) (hints_cons _ _ _ (der_139327 v h) (hints_cons _ _ _ (der_139333 v h) (hints_cons _ _ _ (der_139334 v h) (hints_cons _ _ _ (der_139337 v h) (hints_cons _ _ _ (der_139338 v h) (hints_cons _ _ _ (der_139339 v h) (hints_cons _ _ _ (der_139341 v h) (hints_cons _ _ _ (der_139352 v h) (hints_cons _ _ _ (der_139354 v h) (hints_cons _ _ _ (der_139358 v h) (hints_cons _ _ _ (der_139362 v h) (hints_cons _ _ _ (der_139363 v h) (hints_cons _ _ _ (der_139366 v h) (hints_cons _ _ _ (der_139371 v h) (hints_cons _ _ _ (der_139374 v h) (hints_cons _ _ _ (der_139377 v h) (hints_cons _ _ _ (der_139388 v h) (hints_cons _ _ _ (der_139391 v h) (hints_cons _ _ _ (der_139396 v h) (hints_cons _ _ _ (der_139399 v h) (hints_cons _ _ _ (der_139404 v h) (hints_cons _ _ _ (der_139405 v h) (hints_cons _ _ _ (der_139407 v h) (hints_cons _ _ _ (der_139416 v h) (hints_cons _ _ _ (der_139425 v h) (hints_cons _ _ _ (der_139426 v h) (hints_cons _ _ _ (der_139427 v h) (hints_cons _ _ _ (der_139434 v h) (hints_cons _ _ _ (der_139435 v h) (hints_cons _ _ _ (der_139440 v h) (hints_cons _ _ _ (der_139456 v h) (hints_cons _ _ _ (der_139457 v h) (hints_cons _ _ _ (der_139458 v h) (hints_cons _ _ _ (der_139461 v h) (hints_cons _ _ _ (der_139468 v h) (hints_cons _ _ _ (der_139508 v h) (hints_cons _ _ _ (der_139514 v h) (hints_cons _ _ _ (der_139516 v h) (hints_cons _ _ _ (der_139539 v h) (hints_cons _ _ _ (der_139559 v h) (hints_cons _ _ _ (der_139560 v h) (hints_cons _ _ _ (der_139561 v h) (hints_cons _ _ _ (der_139579 v h) (hints_cons _ _ _ (der_139586 v h) (hints_cons _ _ _ (der_139619 v h) (hints_cons _ _ _ (der_139686 v h) (hints_cons _ _ _ (der_139704 v h) (hints_cons _ _ _ (der_139751 v h) (hints_cons _ _ _ (der_139768 v h) (hints_cons _ _ _ (der_139769 v h) (hints_cons _ _ _ (der_139770 v h) (hints_cons _ _ _ (der_139771 v h) (hints_cons _ _ _ (der_139772 v h) (hints_cons _ _ _ (der_139773 v h) (hints_cons _ _ _ (der_139774 v h) (hints_cons _ _ _ (der_139775 v h) (hints_cons _ _ _ (der_139776 v h) (hints_cons _ _ _ (der_139777 v h) (hints_cons _ _ _ (der_139778 v h) (hints_cons _ _ _ (der_139779 v h) (hints_cons _ _ _ (der_139780 v h) (hints_cons _ _ _ (der_139781 v h) (hints_cons _ _ _ (der_139782 v h) (hints_cons _ _ _ (der_139783 v h) (hints_cons _ _ _ (der_139784 v h) (hints_cons _ _ _ (der_139785 v h) (hints_cons _ _ _ (der_139786 v h) (hints_cons _ _ _ (der_139787 v h) (hints_cons _ _ _ (der_139788 v h) (hints_cons _ _ _ (der_139789 v h) (hints_cons _ _ _ (der_139790 v h) (hints_cons _ _ _ (der_139791 v h) (hints_cons _ _ _ (der_139792 v h) (hints_cons _ _ _ (der_139793 v h) (hints_cons _ _ _ (der_139794 v h) (hints_cons _ _ _ (der_139795 v h) (hints_cons _ _ _ (der_139796 v h) (hints_cons _ _ _ (der_139797 v h) (hints_cons _ _ _ (der_139798 v h) (hints_cons _ _ _ (der_139799 v h) (hints_cons _ _ _ (der_139800 v h) (hints_cons _ _ _ (der_139801 v h) (hints_cons _ _ _ (der_139802 v h) (hints_cons _ _ _ (der_139803 v h) (hints_cons _ _ _ (der_139804 v h) (hints_cons _ _ _ (der_139805 v h) (hints_cons _ _ _ (der_139806 v h) (hints_cons _ _ _ (der_139807 v h) (hints_cons _ _ _ (der_139808 v h) (hints_cons _ _ _ (der_139809 v h) (hints_cons _ _ _ (der_139810 v h) (hints_cons _ _ _ (der_139811 v h) (hints_cons _ _ _ (der_139812 v h) (hints_cons _ _ _ (der_139813 v h) (hints_cons _ _ _ (der_139814 v h) (hints_cons _ _ _ (der_139815 v h) (hints_cons _ _ _ (der_139816 v h) (hints_cons _ _ _ (der_139817 v h) (hints_cons _ _ _ (der_139819 v h) (hints_cons _ _ _ (der_139820 v h) (hints_cons _ _ _ (der_139821 v h) (hints_cons _ _ _ (der_139823 v h) (hints_cons _ _ _ (der_139824 v h) (hints_cons _ _ _ (der_139825 v h) (hints_cons _ _ _ (der_139827 v h) (hints_cons _ _ _ (der_139828 v h) (hints_cons _ _ _ (der_139830 v h) (hints_cons _ _ _ (der_139831 v h) (hints_cons _ _ _ (der_139833 v h) (hints_cons _ _ _ (der_139834 v h) (hints_cons _ _ _ (der_139836 v h) (hints_cons _ _ _ (der_139837 v h) (hints_cons _ _ _ (der_139838 v h) (hints_cons _ _ _ (der_139839 v h) (hints_cons _ _ _ (der_139840 v h) (hints_cons _ _ _ (der_139841 v h) (hints_cons _ _ _ (der_139842 v h) (hints_cons _ _ _ (der_139843 v h) (hints_cons _ _ _ (der_139844 v h) (hints_cons _ _ _ (der_139845 v h) (hints_cons _ _ _ (der_139846 v h) (hints_cons _ _ _ (der_139847 v h) (hints_cons _ _ _ (der_139848 v h) (hints_cons _ _ _ (der_139849 v h) (hints_cons _ _ _ (der_139851 v h) (hints_cons _ _ _ (der_139852 v h) (hints_cons _ _ _ (der_139853 v h) (hints_cons _ _ _ (der_139854 v h) (hints_cons _ _ _ (der_139855 v h) (hints_cons _ _ _ (der_139856 v h) (hints_cons _ _ _ (der_139857 v h) (hints_cons _ _ _ (der_139858 v h) (hints_cons _ _ _ (der_139859 v h) (hints_cons _ _ _ (der_139860 v h) (hints_cons _ _ _ (der_139862 v h) (hints_cons _ _ _ (der_139863 v h) (hints_cons _ _ _ (der_139865 v h) (hints_cons _ _ _ (der_139866 v h) (hints_cons _ _ _ (der_139867 v h) (hints_cons _ _ _ (der_139868 v h) (hints_cons _ _ _ (der_139869 v h) (hints_cons _ _ _ (der_139870 v h) (hints_cons _ _ _ (der_139872 v h) (hints_cons _ _ _ (der_139873 v h) (hints_cons _ _ _ (der_139874 v h) (hints_cons _ _ _ (der_139875 v h) (hints_cons _ _ _ (der_139876 v h) (hints_cons _ _ _ (der_139877 v h) (hints_cons _ _ _ (der_139878 v h) (hints_cons _ _ _ (der_139879 v h) (hints_cons _ _ _ (der_139880 v h) (hints_cons _ _ _ (der_139881 v h) (hints_cons _ _ _ (der_139882 v h) (hints_cons _ _ _ (der_139884 v h) (hints_cons _ _ _ (der_139888 v h) (hints_cons _ _ _ (der_139891 v h) (hints_cons _ _ _ (der_139893 v h) (hints_cons _ _ _ (der_139894 v h) (hints_cons _ _ _ (der_139895 v h) (hints_cons _ _ _ (der_139896 v h) (hints_cons _ _ _ (der_139897 v h) (hints_cons _ _ _ (der_139898 v h) (hints_cons _ _ _ (der_139899 v h) (hints_cons _ _ _ (der_139900 v h) (hints_cons _ _ _ (der_139901 v h) (hints_cons _ _ _ (der_139902 v h) (hints_cons _ _ _ (der_139904 v h) (hints_cons _ _ _ (der_139905 v h) (hints_cons _ _ _ (der_139906 v h) (hints_cons _ _ _ (der_139907 v h) (hints_cons _ _ _ (der_139908 v h) (hints_cons _ _ _ (der_139910 v h) (hints_cons _ _ _ (der_139911 v h) (hints_cons _ _ _ (der_139913 v h) (hints_cons _ _ _ (der_139914 v h) (hints_cons _ _ _ (der_139915 v h) (hints_cons _ _ _ (der_139917 v h) (hints_cons _ _ _ (der_139919 v h) (hints_cons _ _ _ (der_139920 v h) (hints_cons _ _ _ (der_139921 v h) (hints_cons _ _ _ (der_139922 v h) (hints_cons _ _ _ (der_139924 v h) (hints_cons _ _ _ (der_139925 v h) (hints_cons _ _ _ (der_139926 v h) (hints_cons _ _ _ (der_139927 v h) (hints_cons _ _ _ (der_139928 v h) (hints_cons _ _ _ (der_139931 v h) (hints_cons _ _ _ (der_139932 v h) (hints_cons _ _ _ (der_139933 v h) (hints_cons _ _ _ (der_139934 v h) (hints_cons _ _ _ (der_139935 v h) (hints_cons _ _ _ (der_139936 v h) (hints_cons _ _ _ (der_139938 v h) (hints_cons _ _ _ (der_139939 v h) (hints_cons _ _ _ (der_139940 v h) (hints_cons _ _ _ (der_139941 v h) (hints_cons _ _ _ (der_139942 v h) (hints_cons _ _ _ (der_139943 v h) (hints_cons _ _ _ (der_139944 v h) (hints_cons _ _ _ (der_139945 v h) (hints_cons _ _ _ (der_139946 v h) (hints_cons _ _ _ (der_139947 v h) (hints_cons _ _ _ (der_139948 v h) (hints_cons _ _ _ (der_139949 v h) (hints_cons _ _ _ (der_139950 v h) (hints_cons _ _ _ (der_139951 v h) (hints_cons _ _ _ (der_139954 v h) (hints_cons _ _ _ (der_139955 v h) (hints_cons _ _ _ (der_139956 v h) (hints_cons _ _ _ (der_139957 v h) (hints_cons _ _ _ (der_139959 v h) (hints_cons _ _ _ (der_139960 v h) (hints_cons _ _ _ (der_139961 v h) (hints_cons _ _ _ (der_139962 v h) (hints_cons _ _ _ (der_139963 v h) (hints_cons _ _ _ (der_139964 v h) (hints_cons _ _ _ (der_139965 v h) (hints_cons _ _ _ (der_139966 v h) (hints_cons _ _ _ (der_139968 v h) (hints_cons _ _ _ (der_139969 v h) (hints_cons _ _ _ (der_139970 v h) (hints_cons _ _ _ (der_139971 v h) (hints_cons _ _ _ (der_139972 v h) (hints_cons _ _ _ (der_139973 v h) (hints_cons _ _ _ (der_139974 v h) (hints_cons _ _ _ (der_139975 v h) (hints_cons _ _ _ (der_139976 v h) (hints_cons _ _ _ (der_139977 v h) (hints_cons _ _ _ (der_139978 v h) (hints_cons _ _ _ (der_139979 v h) (hints_cons _ _ _ (der_139980 v h) (hints_cons _ _ _ (der_139981 v h) (hints_cons _ _ _ (der_139982 v h) (hints_cons _ _ _ (der_139983 v h) (hints_cons _ _ _ (der_139984 v h) (hints_cons _ _ _ (der_139985 v h) (hints_cons _ _ _ (der_139986 v h) (hints_cons _ _ _ (der_139987 v h) (hints_cons _ _ _ (der_139988 v h) (hints_cons _ _ _ (der_139989 v h) (hints_cons _ _ _ (der_139991 v h) (hints_cons _ _ _ (der_139993 v h) (hints_cons _ _ _ (der_139994 v h) (hints_cons _ _ _ (der_139995 v h) (hints_cons _ _ _ (der_139996 v h) (hints_cons _ _ _ (der_139997 v h) (hints_cons _ _ _ (der_139998 v h) (hints_cons _ _ _ (der_139999 v h) (hints_cons _ _ _ (der_140000 v h) (hints_cons _ _ _ (der_140001 v h) (hints_cons _ _ _ (der_140002 v h) (hints_cons _ _ _ (der_140003 v h) (hints_cons _ _ _ (der_140006 v h) (hints_cons _ _ _ (der_140007 v h) (hints_cons _ _ _ (der_140008 v h) (hints_cons _ _ _ (der_140009 v h) (hints_cons _ _ _ (der_140010 v h) (hints_cons _ _ _ (der_140012 v h) (hints_cons _ _ _ (der_140013 v h) (hints_cons _ _ _ (der_140015 v h) (hints_cons _ _ _ (der_140016 v h) (hints_cons _ _ _ (der_140017 v h) (hints_cons _ _ _ (der_140019 v h) (hints_cons _ _ _ (der_140020 v h) (hints_cons _ _ _ (der_140021 v h) (hints_cons _ _ _ (der_140022 v h) (hints_cons _ _ _ (der_140024 v h) (hints_cons _ _ _ (der_140025 v h) (hints_cons _ _ _ (der_140026 v h) (hints_cons _ _ _ (der_140027 v h) (hints_cons _ _ _ (der_140030 v h) (hints_cons _ _ _ (der_140031 v h) (hints_cons _ _ _ (der_140032 v h) (hints_cons _ _ _ (der_140033 v h) (hints_cons _ _ _ (der_140034 v h) (hints_cons _ _ _ (der_140035 v h) (hints_cons _ _ _ (der_140036 v h) (hints_cons _ _ _ (der_140037 v h) (hints_cons _ _ _ (der_140038 v h) (hints_cons _ _ _ (der_140039 v h) (hints_cons _ _ _ (der_140040 v h) (hints_cons _ _ _ (der_140042 v h) (hints_cons _ _ _ (der_140043 v h) (hints_cons _ _ _ (der_140044 v h) (hints_cons _ _ _ (der_140045 v h) (hints_cons _ _ _ (der_140046 v h) (hints_cons _ _ _ (der_140048 v h) (hints_cons _ _ _ (der_140049 v h) (hints_cons _ _ _ (der_140050 v h) (hints_cons _ _ _ (der_140051 v h) (hints_cons _ _ _ (der_140052 v h) (hints_cons _ _ _ (der_140053 v h) (hints_cons _ _ _ (der_140054 v h) (hints_cons _ _ _ (der_140055 v h) (hints_cons _ _ _ (der_140056 v h) (hints_cons _ _ _ (der_140057 v h) (hints_cons _ _ _ (der_140058 v h) (hints_cons _ _ _ (der_140059 v h) (hints_cons _ _ _ (der_140060 v h) (hints_cons _ _ _ (der_140061 v h) (hints_cons _ _ _ (der_140063 v h) (hints_cons _ _ _ (der_140064 v h) (hints_cons _ _ _ (der_140065 v h) (hints_cons _ _ _ (der_140066 v h) (hints_cons _ _ _ (der_140067 v h) (hints_cons _ _ _ (der_140068 v h) (hints_cons _ _ _ (der_140069 v h) (hints_cons _ _ _ (der_140070 v h) (hints_cons _ _ _ (der_140071 v h) (hints_cons _ _ _ (der_140072 v h) (hints_cons _ _ _ (der_140073 v h) (hints_cons _ _ _ (der_140074 v h) (hints_cons _ _ _ (der_140075 v h) (hints_cons _ _ _ (der_140076 v h) (hints_cons _ _ _ (der_140077 v h) (hints_cons _ _ _ (der_140078 v h) (hints_cons _ _ _ (der_140079 v h) (hints_cons _ _ _ (der_140080 v h) (hints_cons _ _ _ (der_140081 v h) (hints_cons _ _ _ (der_140082 v h) (hints_cons _ _ _ (der_140083 v h) (hints_cons _ _ _ (der_140084 v h) (hints_cons _ _ _ (der_140085 v h) (hints_cons _ _ _ (der_140086 v h) (hints_cons _ _ _ (der_140087 v h) (hints_cons _ _ _ (der_140088 v h) (hints_cons _ _ _ (der_140089 v h) (hints_cons _ _ _ (der_140090 v h) (hints_cons _ _ _ (der_140091 v h) (hints_cons _ _ _ (der_140092 v h) (hints_cons _ _ _ (der_140093 v h) (hints_cons _ _ _ (der_140094 v h) (hints_cons _ _ _ (der_140095 v h) (hints_cons _ _ _ (der_140096 v h) (hints_cons _ _ _ (der_140097 v h) (hints_cons _ _ _ (der_140098 v h) (hints_cons _ _ _ (der_140099 v h) (hints_cons _ _ _ (der_140100 v h) (hints_cons _ _ _ (der_140101 v h) (hints_cons _ _ _ (der_140102 v h) (hints_cons _ _ _ (der_140103 v h) (hints_cons _ _ _ (der_140104 v h) (hints_cons _ _ _ (der_140105 v h) (hints_cons _ _ _ (der_140107 v h) (hints_cons _ _ _ (der_140109 v h) (hints_cons _ _ _ (der_140110 v h) (hints_cons _ _ _ (der_140111 v h) (hints_cons _ _ _ (der_140112 v h) (hints_cons _ _ _ (der_140113 v h) (hints_cons _ _ _ (der_140114 v h) (hints_cons _ _ _ (der_140116 v h) (hints_cons _ _ _ (der_140118 v h) (hints_cons _ _ _ (der_140120 v h) (hints_cons _ _ _ (der_140121 v h) (hints_cons _ _ _ (der_140124 v h) (hints_cons _ _ _ (der_140125 v h) (hints_cons _ _ _ (der_140126 v h) (hints_cons _ _ _ (der_140127 v h) (hints_cons _ _ _ (der_140128 v h) (hints_cons _ _ _ (der_140132 v h) (hints_cons _ _ _ (der_140133 v h) (hints_cons _ _ _ (der_140135 v h) (hints_cons _ _ _ (der_140136 v h) (hints_cons _ _ _ (der_140137 v h) (hints_cons _ _ _ (der_140139 v h) (hints_cons _ _ _ (der_140140 v h) (hints_cons _ _ _ (der_140141 v h) (hints_cons _ _ _ (der_140142 v h) (hints_cons _ _ _ (der_140143 v h) (hints_cons _ _ _ (der_140146 v h) (hints_cons _ _ _ (der_140147 v h) (hints_cons _ _ _ (der_140149 v h) (hints_cons _ _ _ (der_140150 v h) (hints_cons _ _ _ (der_140151 v h) (hints_cons _ _ _ (der_140152 v h) (hints_cons _ _ _ (der_140153 v h) (hints_cons _ _ _ (der_140154 v h) (hints_cons _ _ _ (der_140155 v h) (hints_cons _ _ _ (der_140156 v h) (hints_cons _ _ _ (der_140158 v h) (hints_cons _ _ _ (der_140159 v h) (hints_cons _ _ _ (der_140160 v h) (hints_cons _ _ _ (der_140163 v h) (hints_cons _ _ _ (der_140164 v h) (hints_cons _ _ _ (der_140165 v h) (hints_cons _ _ _ (der_140166 v h) (hints_cons _ _ _ (der_140167 v h) (hints_cons _ _ _ (der_140168 v h) (hints_cons _ _ _ (der_140169 v h) (hints_cons _ _ _ (der_140170 v h) (hints_cons _ _ _ (der_140171 v h) (hints_cons _ _ _ (der_140172 v h) (hints_cons _ _ _ (der_140175 v h) (hints_cons _ _ _ (der_140176 v h) (hints_cons _ _ _ (der_140177 v h) (hints_cons _ _ _ (der_140178 v h) (hints_cons _ _ _ (der_140179 v h) (hints_cons _ _ _ (der_140180 v h) (hints_cons _ _ _ (der_140181 v h) (hints_cons _ _ _ (der_140182 v h) (hints_cons _ _ _ (der_140183 v h) (hints_cons _ _ _ (der_140184 v h) (hints_cons _ _ _ (der_140185 v h) (hints_cons _ _ _ (der_140186 v h) (hints_cons _ _ _ (der_140187 v h) (hints_cons _ _ _ (der_140188 v h) (hints_cons _ _ _ (der_140189 v h) (hints_cons _ _ _ (der_140190 v h) (hints_cons _ _ _ (der_140192 v h) (hints_cons _ _ _ (der_140193 v h) (hints_cons _ _ _ (der_140194 v h) (hints_cons _ _ _ (der_140195 v h) (hints_cons _ _ _ (der_140196 v h) (hints_cons _ _ _ (der_140197 v h) (hints_cons _ _ _ (der_140198 v h) (hints_cons _ _ _ (der_140200 v h) (hints_cons _ _ _ (der_140201 v h) (hints_cons _ _ _ (der_140202 v h) (hints_cons _ _ _ (der_140203 v h) (hints_cons _ _ _ (der_140204 v h) (hints_cons _ _ _ (der_140206 v h) (hints_cons _ _ _ (der_140207 v h) (hints_cons _ _ _ (der_140208 v h) (hints_cons _ _ _ (der_140209 v h) (hints_cons _ _ _ (der_140210 v h) (hints_cons _ _ _ (der_140211 v h) (hints_cons _ _ _ (der_140212 v h) (hints_cons _ _ _ (der_140214 v h) (hints_cons _ _ _ (der_140215 v h) (hints_cons _ _ _ (der_140217 v h) (hints_cons _ _ _ (der_140218 v h) (hints_cons _ _ _ (der_140219 v h) (hints_cons _ _ _ (der_140221 v h) (hints_cons _ _ _ (der_140226 v h) (hints_cons _ _ _ (der_140227 v h) (hints_cons _ _ _ (der_140228 v h) (hints_cons _ _ _ (der_140229 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix184 := prefix183 ++ chunk184
theorem prefix_sound184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix184, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound183 v h c hc
  · exact chunk_sound184 v h c hc
end Percolation.NReplay
