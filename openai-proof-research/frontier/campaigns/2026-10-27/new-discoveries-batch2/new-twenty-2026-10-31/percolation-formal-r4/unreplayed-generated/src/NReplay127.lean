import NReplay126
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_106224 : CNF.NClause := [(126,false),(33,true),(64,false),(69,false),(84,false),(4,false)]
theorem der_106224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106224 :=
  CNF.rup_sound cl_106224 [cl_91279,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91279 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106226 : CNF.NClause := [(126,false),(33,true),(64,false),(87,false),(69,false),(84,false)]
theorem der_106226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106226 :=
  CNF.rup_sound cl_106226 [cl_90177,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90177 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106228 : CNF.NClause := [(28,false),(57,true),(18,false),(150,false),(71,false),(79,false)]
theorem der_106228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106228 :=
  CNF.rup_sound cl_106228 [cl_96880,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96880 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_106229 : CNF.NClause := [(50,true),(143,false),(77,false),(28,false),(85,false),(63,false)]
theorem der_106229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106229 :=
  CNF.rup_sound cl_106229 [cl_98154,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98154 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106230 : CNF.NClause := [(109,true),(46,false),(137,false),(129,false),(146,false),(131,true)]
theorem der_106230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106230 :=
  CNF.rup_sound cl_106230 [cl_101715,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101715 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106232 : CNF.NClause := [(143,false),(138,false),(142,true),(141,true),(84,false),(140,true)]
theorem der_106232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106232 :=
  CNF.rup_sound cl_106232 [cl_103161,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103161 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_106235 : CNF.NClause := [(50,true),(143,false),(17,false),(85,false),(63,false),(22,false)]
theorem der_106235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106235 :=
  CNF.rup_sound cl_106235 [cl_103628,cl_67563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103628 v h) (hints_cons _ _ _ (der_67563 v h) (by intro d hd; cases hd)))
def cl_106236 : CNF.NClause := [(14,false),(47,true),(68,false),(140,false),(84,false),(75,false)]
theorem der_106236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106236 :=
  CNF.rup_sound cl_106236 [cl_103802,cl_56322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103802 v h) (hints_cons _ _ _ (der_56322 v h) (by intro d hd; cases hd)))
def cl_106237 : CNF.NClause := [(120,true),(140,false),(66,false),(84,false),(138,false),(75,false)]
theorem der_106237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106237 :=
  CNF.rup_sound cl_106237 [cl_103845,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103845 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_106238 : CNF.NClause := [(21,false),(141,false),(77,false),(70,false),(48,true),(83,false)]
theorem der_106238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106238 :=
  CNF.rup_sound cl_106238 [cl_104546,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104546 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_106239 : CNF.NClause := [(29,false),(141,false),(70,false),(18,false),(48,true),(83,false)]
theorem der_106239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106239 :=
  CNF.rup_sound cl_106239 [cl_104577,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104577 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_106240 : CNF.NClause := [(122,false),(49,true),(57,true),(85,false),(150,false),(37,true)]
theorem der_106240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106240 :=
  CNF.rup_sound cl_106240 [cl_104586,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104586 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_106241 : CNF.NClause := [(29,false),(141,false),(15,false),(70,false),(48,true),(83,false)]
theorem der_106241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106241 :=
  CNF.rup_sound cl_106241 [cl_104619,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104619 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_106242 : CNF.NClause := [(40,true),(21,false),(133,false),(75,false),(82,false),(63,false)]
theorem der_106242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106242 :=
  CNF.rup_sound cl_106242 [cl_104738,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104738 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_106243 : CNF.NClause := [(21,false),(141,false),(139,true),(70,false),(48,true),(83,false)]
theorem der_106243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106243 :=
  CNF.rup_sound cl_106243 [cl_104879,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104879 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_106244 : CNF.NClause := [(921,false),(64,false),(53,true),(86,false),(90,false),(78,false)]
theorem der_106244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106244 :=
  CNF.rup_sound cl_106244 [cl_105353,cl_93635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105353 v h) (hints_cons _ _ _ (der_93635 v h) (by intro d hd; cases hd)))
def cl_106245 : CNF.NClause := [(55,true),(148,false),(22,true),(6,true),(145,true),(80,false),(18,false)]
theorem der_106245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106245 :=
  CNF.rup_sound cl_106245 [cl_80526,cl_62592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80526 v h) (hints_cons _ _ _ (der_62592 v h) (by intro d hd; cases hd)))
def cl_106246 : CNF.NClause := [(55,true),(148,false),(80,false),(63,false),(147,true),(91,false),(22,true)]
theorem der_106246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106246 :=
  CNF.rup_sound cl_106246 [cl_80531,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80531 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_106253 : CNF.NClause := [(70,true),(128,true),(132,false),(131,true),(129,true),(148,true),(143,true)]
theorem der_106253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106253 :=
  CNF.rup_sound cl_106253 [cl_80549,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80549 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_106256 : CNF.NClause := [(132,true),(69,true),(129,true),(150,true),(136,true),(131,true),(148,true)]
theorem der_106256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106256 :=
  CNF.rup_sound cl_106256 [cl_78803,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78803 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106260 : CNF.NClause := [(81,true),(135,true),(150,true),(126,true),(144,true),(153,true),(142,false)]
theorem der_106260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106260 :=
  CNF.rup_sound cl_106260 [cl_80556,cl_81199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80556 v h) (hints_cons _ _ _ (der_81199 v h) (by intro d hd; cases hd)))
def cl_106262 : CNF.NClause := [(134,true),(136,true),(38,true),(135,true),(137,false),(131,false),(73,false)]
theorem der_106262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106262 :=
  CNF.rup_sound cl_106262 [cl_72319,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72319 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_106263 : CNF.NClause := [(89,false),(147,false),(81,false),(11,true),(65,false),(74,false),(54,true)]
theorem der_106263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106263 :=
  CNF.rup_sound cl_106263 [cl_82006,cl_63040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82006 v h) (hints_cons _ _ _ (der_63040 v h) (by intro d hd; cases hd)))
def cl_106265 : CNF.NClause := [(111,true),(38,false),(148,false),(88,false),(151,false),(152,true),(84,false)]
theorem der_106265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106265 :=
  CNF.rup_sound cl_106265 [cl_83245,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83245 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_106266 : CNF.NClause := [(15,true),(77,true),(16,false),(68,true),(12,true),(4,true),(18,true)]
theorem der_106266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106266 :=
  CNF.rup_sound cl_106266 [cl_87766,cl_76570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87766 v h) (hints_cons _ _ _ (der_76570 v h) (by intro d hd; cases hd)))
def cl_106267 : CNF.NClause := [(93,false),(60,false),(119,false),(146,false),(105,false),(132,false),(111,false)]
theorem der_106267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106267 :=
  CNF.rup_sound cl_106267 [cl_86106,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86106 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106268 : CNF.NClause := [(97,false),(115,false),(47,false),(146,false),(120,false),(132,false),(108,false)]
theorem der_106268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106268 :=
  CNF.rup_sound cl_106268 [cl_86382,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86382 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106269 : CNF.NClause := [(82,true),(76,true),(5,true),(10,true),(1,true),(24,true),(8,false)]
theorem der_106269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106269 :=
  CNF.rup_sound cl_106269 [cl_86614,cl_29851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86614 v h) (hints_cons _ _ _ (der_29851 v h) (by intro d hd; cases hd)))
def cl_106270 : CNF.NClause := [(113,false),(57,false),(49,false),(55,false),(132,false),(47,false),(146,false)]
theorem der_106270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106270 :=
  CNF.rup_sound cl_106270 [cl_87387,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87387 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106271 : CNF.NClause := [(99,true),(51,false),(136,false),(88,false),(151,false),(152,true),(85,false)]
theorem der_106271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106271 :=
  CNF.rup_sound cl_106271 [cl_89579,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89579 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_106272 : CNF.NClause := [(108,false),(100,false),(104,false),(49,false),(122,false),(146,false),(132,false)]
theorem der_106272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106272 :=
  CNF.rup_sound cl_106272 [cl_87401,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87401 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106273 : CNF.NClause := [(905,true),(75,true),(901,true),(903,true),(920,true),(925,true),(910,true)]
theorem der_106273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106273 :=
  CNF.rup_sound cl_106273 [cl_93644,cl_105705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93644 v h) (hints_cons _ _ _ (der_105705 v h) (by intro d hd; cases hd)))
def cl_106274 : CNF.NClause := [(111,false),(112,false),(123,false),(110,false),(142,false),(130,false),(46,false)]
theorem der_106274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106274 :=
  CNF.rup_sound cl_106274 [cl_95026,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95026 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_106275 : CNF.NClause := [(27,false),(62,true),(69,true),(405,true),(18,true),(1080,true),(1083,true)]
theorem der_106275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106275 :=
  CNF.rup_sound cl_106275 [cl_93147,cl_76613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93147 v h) (hints_cons _ _ _ (der_76613 v h) (by intro d hd; cases hd)))
def cl_106279 : CNF.NClause := [(905,false),(82,true),(76,false),(65,false),(90,false),(68,false),(79,false)]
theorem der_106279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106279 :=
  CNF.rup_sound cl_106279 [cl_92155,cl_91955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92155 v h) (hints_cons _ _ _ (der_91955 v h) (by intro d hd; cases hd)))
def cl_106281 : CNF.NClause := [(68,true),(76,true),(27,true),(29,true),(8,false),(24,true),(10,true)]
theorem der_106281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106281 :=
  CNF.rup_sound cl_106281 [cl_97412,cl_76637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97412 v h) (hints_cons _ _ _ (der_76637 v h) (by intro d hd; cases hd)))
def cl_106282 : CNF.NClause := [(59,false),(49,false),(109,false),(50,false),(42,false),(153,false),(137,false)]
theorem der_106282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106282 :=
  CNF.rup_sound cl_106282 [cl_95547,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95547 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106283 : CNF.NClause := [(920,false),(85,false),(66,false),(73,false),(52,true),(923,true),(79,false)]
theorem der_106283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106283 :=
  CNF.rup_sound cl_106283 [cl_97044,cl_105706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97044 v h) (hints_cons _ _ _ (der_105706 v h) (by intro d hd; cases hd)))
def cl_106285 : CNF.NClause := [(137,false),(153,false),(114,false),(118,false),(94,false),(104,false),(35,false)]
theorem der_106285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106285 :=
  CNF.rup_sound cl_106285 [cl_100415,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100415 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106286 : CNF.NClause := [(59,false),(45,false),(50,false),(137,false),(34,false),(35,false),(153,false)]
theorem der_106286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106286 :=
  CNF.rup_sound cl_106286 [cl_98020,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98020 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106288 : CNF.NClause := [(908,false),(133,true),(18,true),(82,false),(81,false),(40,true),(63,false)]
theorem der_106288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106288 :=
  CNF.rup_sound cl_106288 [cl_104378,cl_93640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104378 v h) (hints_cons _ _ _ (der_93640 v h) (by intro d hd; cases hd)))
def cl_106289 : CNF.NClause := [(137,false),(153,false),(106,false),(57,false),(110,false),(122,false),(114,false)]
theorem der_106289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106289 :=
  CNF.rup_sound cl_106289 [cl_104536,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104536 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106290 : CNF.NClause := [(135,false),(104,false),(94,false),(146,false),(118,false),(99,false),(35,false)]
theorem der_106290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106290 :=
  CNF.rup_sound cl_106290 [cl_104940,cl_85856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104940 v h) (hints_cons _ _ _ (der_85856 v h) (by intro d hd; cases hd)))
def cl_106291 : CNF.NClause := [(38,true),(906,false),(915,true),(131,false),(71,false),(82,false),(73,false)]
theorem der_106291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106291 :=
  CNF.rup_sound cl_106291 [cl_105456,cl_72318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105456 v h) (hints_cons _ _ _ (der_72318 v h) (by intro d hd; cases hd)))
def cl_106292 : CNF.NClause := [(22,false),(21,false),(78,false),(90,false),(64,false),(86,false),(75,false),(53,true)]
theorem der_106292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106292 :=
  CNF.rup_sound cl_106292 [cl_38154,cl_96718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38154 v h) (hints_cons _ _ _ (der_96718 v h) (by intro d hd; cases hd)))
def cl_106296 : CNF.NClause := [(6,false),(66,true),(137,true),(132,true),(129,true),(141,true),(131,true),(153,true)]
theorem der_106296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106296 :=
  CNF.rup_sound cl_106296 [cl_78868,cl_105702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78868 v h) (hints_cons _ _ _ (der_105702 v h) (by intro d hd; cases hd)))
def cl_106298 : CNF.NClause := [(925,false),(28,false),(6,true),(57,true),(27,false),(71,false),(83,false),(79,false)]
theorem der_106298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106298 :=
  CNF.rup_sound cl_106298 [cl_44453,cl_94890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44453 v h) (hints_cons _ _ _ (der_94890 v h) (by intro d hd; cases hd)))
def cl_106299 : CNF.NClause := [(92,false),(22,false),(129,false),(3,false),(148,true),(28,true),(126,true),(36,true)]
theorem der_106299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106299 :=
  CNF.rup_sound cl_106299 [cl_80568,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80568 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_106302 : CNF.NClause := [(6,false),(10,false),(81,false),(43,true),(136,false),(85,false),(131,true),(141,true)]
theorem der_106302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106302 :=
  CNF.rup_sound cl_106302 [cl_80574,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80574 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_106304 : CNF.NClause := [(17,false),(65,false),(23,false),(67,false),(89,false),(54,true),(74,false),(81,false)]
theorem der_106304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106304 :=
  CNF.rup_sound cl_106304 [cl_62683,cl_82775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62683 v h) (hints_cons _ _ _ (der_82775 v h) (by intro d hd; cases hd)))
def cl_106306 : CNF.NClause := [(1066,false),(1072,true),(1060,true),(43,true),(2,false),(72,false),(85,false),(81,false)]
theorem der_106306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106306 :=
  CNF.rup_sound cl_106306 [cl_80580,cl_15918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80580 v h) (hints_cons _ _ _ (der_15918 v h) (by intro d hd; cases hd)))
def cl_106307 : CNF.NClause := [(136,false),(43,true),(128,true),(131,false),(138,true),(129,true),(132,true),(143,true)]
theorem der_106307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106307 :=
  CNF.rup_sound cl_106307 [cl_73003,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73003 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_106308 : CNF.NClause := [(132,true),(143,true),(151,false),(138,true),(88,true),(128,false),(84,true),(139,true)]
theorem der_106308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106308 :=
  CNF.rup_sound cl_106308 [cl_74290,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74290 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_106312 : CNF.NClause := [(89,true),(132,true),(88,true),(143,true),(151,false),(139,true),(128,false),(84,true)]
theorem der_106312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106312 :=
  CNF.rup_sound cl_106312 [cl_75706,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75706 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_106313 : CNF.NClause := [(28,false),(38,false),(95,true),(24,false),(126,true),(86,false),(141,true),(131,false)]
theorem der_106313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106313 :=
  CNF.rup_sound cl_106313 [cl_83104,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83104 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_106315 : CNF.NClause := [(122,true),(150,false),(64,false),(72,false),(71,false),(136,false),(85,false),(152,true)]
theorem der_106315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106315 :=
  CNF.rup_sound cl_106315 [cl_85861,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85861 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_106316 : CNF.NClause := [(32,true),(33,true),(128,true),(127,true),(29,false),(5,false),(3,false),(71,false)]
theorem der_106316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106316 :=
  CNF.rup_sound cl_106316 [cl_84972,cl_76595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84972 v h) (hints_cons _ _ _ (der_76595 v h) (by intro d hd; cases hd)))
def cl_106317 : CNF.NClause := [(135,false),(109,false),(118,false),(94,false),(35,false),(132,false),(104,false),(80,false)]
theorem der_106317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106317 :=
  CNF.rup_sound cl_106317 [cl_89137,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89137 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106318 : CNF.NClause := [(125,false),(143,true),(37,false),(109,true),(150,true),(88,false),(131,true),(139,false)]
theorem der_106318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106318 :=
  CNF.rup_sound cl_106318 [cl_87225,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87225 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106319 : CNF.NClause := [(913,false),(910,true),(63,false),(72,true),(70,false),(79,false),(86,false),(89,false)]
theorem der_106319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106319 :=
  CNF.rup_sound cl_106319 [cl_88061,cl_15880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88061 v h) (hints_cons _ _ _ (der_15880 v h) (by intro d hd; cases hd)))
def cl_106320 : CNF.NClause := [(117,true),(89,false),(153,true),(125,true),(8,false),(49,false),(142,false),(129,true)]
theorem der_106320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106320 :=
  CNF.rup_sound cl_106320 [cl_87568,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87568 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_106321 : CNF.NClause := [(5,false),(101,false),(97,false),(128,false),(122,false),(113,false),(37,false),(126,false)]
theorem der_106321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106321 :=
  CNF.rup_sound cl_106321 [cl_91275,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91275 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106322 : CNF.NClause := [(144,false),(58,false),(109,false),(120,false),(125,false),(107,false),(129,false),(93,false)]
theorem der_106322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106322 :=
  CNF.rup_sound cl_106322 [cl_93841,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93841 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_106323 : CNF.NClause := [(103,false),(41,false),(123,false),(104,false),(146,false),(132,false),(105,false),(86,false)]
theorem der_106323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106323 :=
  CNF.rup_sound cl_106323 [cl_93540,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93540 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_106324 : CNF.NClause := [(123,false),(113,false),(116,false),(126,false),(117,false),(5,false),(128,false),(36,false)]
theorem der_106324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106324 :=
  CNF.rup_sound cl_106324 [cl_90806,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90806 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106325 : CNF.NClause := [(38,false),(32,false),(128,false),(125,false),(129,false),(45,false),(58,false),(144,false)]
theorem der_106325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106325 :=
  CNF.rup_sound cl_106325 [cl_94021,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94021 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_106326 : CNF.NClause := [(52,false),(60,false),(38,false),(84,false),(132,false),(152,false),(58,false),(54,false)]
theorem der_106326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106326 :=
  CNF.rup_sound cl_106326 [cl_94780,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94780 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106329 : CNF.NClause := [(117,true),(89,false),(32,false),(129,true),(88,false),(146,true),(142,true),(125,false)]
theorem der_106329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106329 :=
  CNF.rup_sound cl_106329 [cl_90228,cl_105759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90228 v h) (hints_cons _ _ _ (der_105759 v h) (by intro d hd; cases hd)))
def cl_106330 : CNF.NClause := [(36,false),(46,false),(45,false),(152,false),(135,false),(49,false),(37,false),(84,false)]
theorem der_106330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106330 :=
  CNF.rup_sound cl_106330 [cl_94966,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94966 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106331 : CNF.NClause := [(55,false),(36,false),(135,false),(132,false),(49,false),(51,false),(46,false),(80,false)]
theorem der_106331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106331 :=
  CNF.rup_sound cl_106331 [cl_101119,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101119 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_106333 : CNF.NClause := [(1055,false),(66,true),(87,false),(32,true),(1075,true),(20,false),(5,false),(81,false)]
theorem der_106333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106333 :=
  CNF.rup_sound cl_106333 [cl_100875,cl_79597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100875 v h) (hints_cons _ _ _ (der_79597 v h) (by intro d hd; cases hd)))
def cl_106335 : CNF.NClause := [(59,false),(145,false),(89,false),(112,true),(148,true),(146,true),(65,false),(139,false)]
theorem der_106335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106335 :=
  CNF.rup_sound cl_106335 [cl_97750,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97750 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106336 : CNF.NClause := [(117,true),(91,false),(138,false),(143,false),(141,true),(73,false),(139,true),(53,false)]
theorem der_106336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106336 :=
  CNF.rup_sound cl_106336 [cl_102181,cl_95938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102181 v h) (hints_cons _ _ _ (der_95938 v h) (by intro d hd; cases hd)))
def cl_106337 : CNF.NClause := [(28,true),(103,true),(139,true),(138,false),(126,true),(137,false),(43,false),(132,true)]
theorem der_106337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106337 :=
  CNF.rup_sound cl_106337 [cl_102269,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102269 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106339 : CNF.NClause := [(111,false),(140,false),(138,false),(96,false),(116,false),(34,false),(118,false),(77,false)]
theorem der_106339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106339 :=
  CNF.rup_sound cl_106339 [cl_103426,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103426 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_106340 : CNF.NClause := [(15,false),(46,true),(80,false),(81,false),(139,true),(18,false),(79,false),(78,false)]
theorem der_106340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106340 :=
  CNF.rup_sound cl_106340 [cl_103449,cl_36157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103449 v h) (hints_cons _ _ _ (der_36157 v h) (by intro d hd; cases hd)))
def cl_106341 : CNF.NClause := [(126,false),(143,true),(48,true),(147,true),(134,true),(142,true),(130,true),(141,false)]
theorem der_106341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106341 :=
  CNF.rup_sound cl_106341 [cl_103546,cl_15783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103546 v h) (hints_cons _ _ _ (der_15783 v h) (by intro d hd; cases hd)))
def cl_106342 : CNF.NClause := [(113,false),(148,false),(99,false),(121,false),(150,false),(96,false),(128,false),(39,false)]
theorem der_106342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106342 :=
  CNF.rup_sound cl_106342 [cl_104439,cl_105700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104439 v h) (hints_cons _ _ _ (der_105700 v h) (by intro d hd; cases hd)))
def cl_106343 : CNF.NClause := [(151,false),(148,true),(139,true),(141,true),(133,true),(58,true),(142,true),(128,false)]
theorem der_106343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106343 :=
  CNF.rup_sound cl_106343 [cl_104469,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104469 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_106344 : CNF.NClause := [(139,true),(126,true),(145,true),(86,true),(133,true),(130,true),(150,false),(131,true)]
theorem der_106344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106344 :=
  CNF.rup_sound cl_106344 [cl_104474,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104474 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106345 : CNF.NClause := [(13,true),(16,false),(11,true),(12,true),(134,false),(72,false),(45,true),(63,false)]
theorem der_106345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106345 :=
  CNF.rup_sound cl_106345 [cl_104731,cl_15777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104731 v h) (hints_cons _ _ _ (der_15777 v h) (by intro d hd; cases hd)))
def cl_106347 : CNF.NClause := [(912,false),(44,true),(911,true),(913,true),(84,false),(71,false),(65,false),(78,false)]
theorem der_106347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106347 :=
  CNF.rup_sound cl_106347 [cl_105152,cl_76539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105152 v h) (hints_cons _ _ _ (der_76539 v h) (by intro d hd; cases hd)))
def cl_106349 : CNF.NClause := [(101,false),(33,false),(42,false),(113,false),(35,false),(37,false),(46,true),(43,false),(110,false)]
theorem der_106349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106349 :=
  CNF.rup_sound cl_106349 [cl_80586,cl_79602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80586 v h) (hints_cons _ _ _ (der_79602 v h) (by intro d hd; cases hd)))
def cl_106351 : CNF.NClause := [(47,true),(89,false),(142,false),(68,false),(84,false),(143,true),(15,true),(141,true),(66,false)]
theorem der_106351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106351 :=
  CNF.rup_sound cl_106351 [cl_38581,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38581 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106355 : CNF.NClause := [(55,true),(148,false),(5,true),(126,true),(4,false),(6,false),(67,false),(13,true),(152,true)]
theorem der_106355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106355 :=
  CNF.rup_sound cl_106355 [cl_78952,cl_105700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78952 v h) (hints_cons _ _ _ (der_105700 v h) (by intro d hd; cases hd)))
def cl_106358 : CNF.NClause := [(86,true),(127,true),(134,true),(129,true),(128,true),(141,true),(137,true),(135,true),(131,true)]
theorem der_106358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106358 :=
  CNF.rup_sound cl_106358 [cl_57648,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57648 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_106361 : CNF.NClause := [(85,true),(135,true),(125,true),(147,true),(133,true),(137,true),(142,true),(140,false),(131,true)]
theorem der_106361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106361 :=
  CNF.rup_sound cl_106361 [cl_80611,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80611 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_106362 : CNF.NClause := [(126,false),(33,true),(84,false),(125,false),(32,true),(7,true),(86,false),(69,false),(143,true)]
theorem der_106362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106362 :=
  CNF.rup_sound cl_106362 [cl_80612,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80612 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106363 : CNF.NClause := [(81,true),(1,true),(917,true),(15,true),(918,true),(906,true),(901,true),(915,true),(921,true)]
theorem der_106363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106363 :=
  CNF.rup_sound cl_106363 [cl_72059,cl_104421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72059 v h) (hints_cons _ _ _ (der_104421 v h) (by intro d hd; cases hd)))
def cl_106364 : CNF.NClause := [(136,true),(144,false),(128,true),(47,true),(132,true),(141,true),(84,false),(153,true),(89,false)]
theorem der_106364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106364 :=
  CNF.rup_sound cl_106364 [cl_73140,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73140 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106366 : CNF.NClause := [(132,true),(148,true),(152,true),(134,true),(71,true),(126,true),(153,true),(142,true),(139,true)]
theorem der_106366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106366 :=
  CNF.rup_sound cl_106366 [cl_80613,cl_95250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80613 v h) (hints_cons _ _ _ (der_95250 v h) (by intro d hd; cases hd)))
def cl_106367 : CNF.NClause := [(122,true),(26,false),(80,false),(83,false),(79,false),(75,false),(148,false),(71,false),(62,false)]
theorem der_106367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106367 :=
  CNF.rup_sound cl_106367 [cl_83232,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83232 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_106368 : CNF.NClause := [(93,true),(59,false),(141,true),(150,true),(148,true),(85,false),(152,false),(88,false),(89,false)]
theorem der_106368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106368 :=
  CNF.rup_sound cl_106368 [cl_82793,cl_87741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82793 v h) (hints_cons _ _ _ (der_87741 v h) (by intro d hd; cases hd)))
def cl_106369 : CNF.NClause := [(10,false),(22,true),(71,false),(148,false),(21,true),(23,true),(69,false),(70,false),(51,true)]
theorem der_106369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106369 :=
  CNF.rup_sound cl_106369 [cl_83464,cl_15788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83464 v h) (hints_cons _ _ _ (der_15788 v h) (by intro d hd; cases hd)))
def cl_106370 : CNF.NClause := [(102,true),(38,false),(147,true),(88,false),(132,true),(78,false),(125,false),(86,false),(142,false)]
theorem der_106370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106370 :=
  CNF.rup_sound cl_106370 [cl_83361,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83361 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106373 : CNF.NClause := [(109,true),(128,true),(146,true),(37,false),(130,false),(88,false),(139,true),(89,false),(76,false)]
theorem der_106373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106373 :=
  CNF.rup_sound cl_106373 [cl_87915,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87915 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_106374 : CNF.NClause := [(907,true),(910,true),(73,true),(908,true),(918,true),(912,true),(914,true),(926,true),(904,false)]
theorem der_106374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106374 :=
  CNF.rup_sound cl_106374 [cl_87323,cl_62084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87323 v h) (hints_cons _ _ _ (der_62084 v h) (by intro d hd; cases hd)))
def cl_106375 : CNF.NClause := [(109,true),(58,false),(144,false),(131,true),(130,false),(88,false),(78,false),(125,true),(143,true)]
theorem der_106375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106375 :=
  CNF.rup_sound cl_106375 [cl_89220,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89220 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_106376 : CNF.NClause := [(119,false),(44,false),(103,false),(132,false),(102,false),(152,false),(109,false),(76,false),(84,false)]
theorem der_106376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106376 :=
  CNF.rup_sound cl_106376 [cl_85217,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85217 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106377 : CNF.NClause := [(89,false),(143,true),(108,true),(78,false),(141,true),(79,false),(20,false),(142,false),(49,false)]
theorem der_106377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106377 :=
  CNF.rup_sound cl_106377 [cl_87004,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87004 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106378 : CNF.NClause := [(1058,false),(86,false),(70,false),(1063,true),(1078,true),(72,false),(79,false),(63,true),(89,false)]
theorem der_106378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106378 :=
  CNF.rup_sound cl_106378 [cl_86792,cl_80208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86792 v h) (hints_cons _ _ _ (der_80208 v h) (by intro d hd; cases hd)))
def cl_106379 : CNF.NClause := [(109,true),(5,false),(58,false),(146,true),(88,false),(151,false),(79,false),(128,true),(130,true)]
theorem der_106379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106379 :=
  CNF.rup_sound cl_106379 [cl_88129,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88129 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_106380 : CNF.NClause := [(110,true),(45,false),(131,true),(134,true),(88,false),(142,true),(132,false),(128,false),(85,false)]
theorem der_106380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106380 :=
  CNF.rup_sound cl_106380 [cl_89169,cl_63081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89169 v h) (hints_cons _ _ _ (der_63081 v h) (by intro d hd; cases hd)))
def cl_106381 : CNF.NClause := [(59,false),(125,false),(86,false),(112,true),(132,false),(137,true),(142,true),(67,false),(89,false)]
theorem der_106381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106381 :=
  CNF.rup_sound cl_106381 [cl_88678,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88678 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106382 : CNF.NClause := [(117,true),(89,false),(125,true),(62,false),(8,false),(88,false),(49,false),(142,false),(129,true)]
theorem der_106382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106382 :=
  CNF.rup_sound cl_106382 [cl_87716,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87716 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_106384 : CNF.NClause := [(105,false),(100,false),(118,false),(63,false),(148,false),(76,false),(110,false),(136,false),(33,false)]
theorem der_106384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106384 :=
  CNF.rup_sound cl_106384 [cl_90272,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90272 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_106385 : CNF.NClause := [(97,false),(103,false),(42,false),(129,false),(86,false),(121,false),(144,false),(135,false),(111,false)]
theorem der_106385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106385 :=
  CNF.rup_sound cl_106385 [cl_95530,cl_105704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95530 v h) (hints_cons _ _ _ (der_105704 v h) (by intro d hd; cases hd)))
def cl_106386 : CNF.NClause := [(59,false),(126,false),(128,false),(131,true),(121,false),(101,false),(112,false),(93,false),(79,false)]
theorem der_106386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106386 :=
  CNF.rup_sound cl_106386 [cl_91701,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91701 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106387 : CNF.NClause := [(119,false),(152,false),(146,false),(84,false),(100,false),(94,false),(40,false),(86,false),(113,false)]
theorem der_106387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106387 :=
  CNF.rup_sound cl_106387 [cl_91380,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91380 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106388 : CNF.NClause := [(50,false),(102,false),(94,false),(116,false),(121,false),(78,false),(86,false),(130,false),(142,false)]
theorem der_106388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106388 :=
  CNF.rup_sound cl_106388 [cl_93597,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93597 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_106389 : CNF.NClause := [(103,false),(112,false),(131,true),(43,false),(128,false),(122,false),(116,false),(126,false),(79,false)]
theorem der_106389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106389 :=
  CNF.rup_sound cl_106389 [cl_91647,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91647 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106390 : CNF.NClause := [(52,false),(119,false),(69,false),(83,false),(146,false),(135,false),(116,false),(110,false),(104,false)]
theorem der_106390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106390 :=
  CNF.rup_sound cl_106390 [cl_91053,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91053 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106391 : CNF.NClause := [(135,false),(104,false),(146,false),(35,false),(99,false),(83,false),(86,false),(94,false),(118,false)]
theorem der_106391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106391 :=
  CNF.rup_sound cl_106391 [cl_92205,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92205 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106394 : CNF.NClause := [(49,false),(51,false),(153,false),(46,false),(58,false),(145,false),(37,false),(135,true),(67,false)]
theorem der_106394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106394 :=
  CNF.rup_sound cl_106394 [cl_94151,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94151 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_106395 : CNF.NClause := [(58,false),(49,false),(43,false),(125,false),(63,false),(38,false),(86,false),(128,false),(37,false)]
theorem der_106395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106395 :=
  CNF.rup_sound cl_106395 [cl_93610,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93610 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106396 : CNF.NClause := [(99,true),(136,false),(64,false),(152,true),(151,false),(35,false),(68,false),(88,false),(85,false)]
theorem der_106396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106396 :=
  CNF.rup_sound cl_106396 [cl_89953,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89953 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_106397 : CNF.NClause := [(122,false),(126,false),(128,false),(101,false),(97,false),(84,false),(37,false),(135,false),(113,false)]
theorem der_106397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106397 :=
  CNF.rup_sound cl_106397 [cl_95544,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95544 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106398 : CNF.NClause := [(120,false),(103,false),(125,false),(128,false),(83,false),(101,false),(110,false),(45,false),(138,false)]
theorem der_106398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106398 :=
  CNF.rup_sound cl_106398 [cl_99603,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99603 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106399 : CNF.NClause := [(117,false),(126,false),(45,false),(101,false),(131,true),(120,false),(128,false),(103,false),(79,false)]
theorem der_106399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106399 :=
  CNF.rup_sound cl_106399 [cl_99798,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99798 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106400 : CNF.NClause := [(123,false),(103,false),(131,true),(41,false),(125,false),(126,false),(106,false),(104,false),(86,false)]
theorem der_106400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106400 :=
  CNF.rup_sound cl_106400 [cl_97291,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97291 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_106401 : CNF.NClause := [(118,false),(106,false),(34,false),(150,true),(101,false),(89,false),(137,false),(151,false),(152,true)]
theorem der_106401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106401 :=
  CNF.rup_sound cl_106401 [cl_100018,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100018 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106403 : CNF.NClause := [(93,false),(144,false),(139,false),(120,false),(71,false),(116,false),(58,false),(107,false),(79,false)]
theorem der_106403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106403 :=
  CNF.rup_sound cl_106403 [cl_96910,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96910 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106404 : CNF.NClause := [(115,false),(144,false),(139,false),(107,false),(71,false),(55,false),(94,false),(122,false),(79,false)]
theorem der_106404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106404 :=
  CNF.rup_sound cl_106404 [cl_97642,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97642 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106405 : CNF.NClause := [(910,true),(9,true),(62,true),(928,true),(69,false),(2,true),(18,true),(925,true),(20,true)]
theorem der_106405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106405 :=
  CNF.rup_sound cl_106405 [cl_99072,cl_15875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99072 v h) (hints_cons _ _ _ (der_15875 v h) (by intro d hd; cases hd)))
def cl_106406 : CNF.NClause := [(123,false),(108,false),(136,false),(46,false),(110,false),(109,false),(64,false),(148,false),(63,false)]
theorem der_106406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106406 :=
  CNF.rup_sound cl_106406 [cl_101252,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101252 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_106407 : CNF.NClause := [(129,false),(126,false),(144,false),(128,false),(49,false),(86,false),(37,false),(43,false),(71,false)]
theorem der_106407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106407 :=
  CNF.rup_sound cl_106407 [cl_96167,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96167 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106409 : CNF.NClause := [(144,false),(106,false),(71,false),(118,false),(116,false),(96,false),(34,false),(139,false),(79,false)]
theorem der_106409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106409 :=
  CNF.rup_sound cl_106409 [cl_98393,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98393 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106410 : CNF.NClause := [(103,false),(144,false),(71,false),(114,false),(97,false),(42,false),(121,false),(139,false),(79,false)]
theorem der_106410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106410 :=
  CNF.rup_sound cl_106410 [cl_100385,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100385 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106411 : CNF.NClause := [(117,false),(144,false),(122,false),(139,false),(49,false),(96,false),(104,false),(71,false),(79,false)]
theorem der_106411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106411 :=
  CNF.rup_sound cl_106411 [cl_100368,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100368 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106414 : CNF.NClause := [(54,false),(105,false),(125,false),(98,false),(96,false),(120,false),(83,false),(128,false),(138,false)]
theorem der_106414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106414 :=
  CNF.rup_sound cl_106414 [cl_100034,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100034 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106415 : CNF.NClause := [(126,false),(37,false),(42,false),(131,true),(49,false),(43,false),(128,false),(50,false),(79,false)]
theorem der_106415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106415 :=
  CNF.rup_sound cl_106415 [cl_99991,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99991 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106416 : CNF.NClause := [(153,false),(46,false),(59,false),(51,false),(42,false),(50,false),(145,false),(73,false),(79,false)]
theorem der_106416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106416 :=
  CNF.rup_sound cl_106416 [cl_95830,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95830 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106417 : CNF.NClause := [(101,false),(46,false),(117,false),(94,false),(120,false),(45,false),(134,false),(78,false),(138,false)]
theorem der_106417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106417 :=
  CNF.rup_sound cl_106417 [cl_101803,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101803 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_106419 : CNF.NClause := [(60,true),(150,true),(139,true),(153,false),(143,true),(148,true),(35,true),(132,true),(138,false)]
theorem der_106419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106419 :=
  CNF.rup_sound cl_106419 [cl_102029,cl_89358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102029 v h) (hints_cons _ _ _ (der_89358 v h) (by intro d hd; cases hd)))
def cl_106421 : CNF.NClause := [(98,false),(53,false),(136,false),(141,true),(109,false),(152,true),(117,false),(150,false),(121,false)]
theorem der_106421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106421 :=
  CNF.rup_sound cl_106421 [cl_102407,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102407 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_106423 : CNF.NClause := [(123,false),(146,false),(15,false),(110,false),(46,false),(111,false),(112,false),(63,false),(143,false)]
theorem der_106423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106423 :=
  CNF.rup_sound cl_106423 [cl_103213,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103213 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_106424 : CNF.NClause := [(146,false),(137,false),(50,false),(141,false),(77,false),(116,false),(94,false),(70,false),(105,false)]
theorem der_106424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106424 :=
  CNF.rup_sound cl_106424 [cl_103241,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103241 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_106426 : CNF.NClause := [(95,false),(115,false),(138,false),(17,false),(151,false),(152,true),(118,false),(33,false),(150,true)]
theorem der_106426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106426 :=
  CNF.rup_sound cl_106426 [cl_103572,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103572 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_106427 : CNF.NClause := [(50,true),(125,true),(137,true),(144,false),(90,false),(131,true),(51,true),(150,true),(63,false)]
theorem der_106427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106427 :=
  CNF.rup_sound cl_106427 [cl_103812,cl_105786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103812 v h) (hints_cons _ _ _ (der_105786 v h) (by intro d hd; cases hd)))
def cl_106428 : CNF.NClause := [(93,false),(57,false),(122,false),(125,false),(126,false),(146,false),(106,false),(79,false),(114,false)]
theorem der_106428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106428 :=
  CNF.rup_sound cl_106428 [cl_103931,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103931 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106429 : CNF.NClause := [(107,false),(121,false),(129,false),(86,false),(99,false),(139,false),(96,false),(78,false),(39,false)]
theorem der_106429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106429 :=
  CNF.rup_sound cl_106429 [cl_104740,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104740 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_106430 : CNF.NClause := [(145,false),(137,false),(94,false),(114,false),(118,false),(99,false),(35,false),(128,false),(79,false)]
theorem der_106430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106430 :=
  CNF.rup_sound cl_106430 [cl_104864,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104864 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106431 : CNF.NClause := [(109,false),(150,false),(94,false),(118,false),(99,false),(35,false),(71,false),(142,false),(152,true)]
theorem der_106431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106431 :=
  CNF.rup_sound cl_106431 [cl_105632,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105632 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_106434 : CNF.NClause := [(921,false),(53,true),(15,true),(64,false),(90,false),(86,false),(923,true),(23,true),(4,false),(6,true)]
theorem der_106434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106434 :=
  CNF.rup_sound cl_106434 [cl_40995,cl_93635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40995 v h) (hints_cons _ _ _ (der_93635 v h) (by intro d hd; cases hd)))
def cl_106440 : CNF.NClause := [(59,false),(137,false),(84,false),(104,false),(153,false),(86,false),(121,false),(101,false),(62,false),(112,false)]
theorem der_106440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106440 :=
  CNF.rup_sound cl_106440 [cl_80631,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80631 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106442 : CNF.NClause := [(143,true),(43,true),(153,false),(134,true),(137,true),(147,true),(129,true),(140,true),(152,true),(136,false)]
theorem der_106442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106442 :=
  CNF.rup_sound cl_106442 [cl_72626,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72626 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_106446 : CNF.NClause := [(127,true),(134,false),(141,true),(41,true),(138,false),(75,false),(152,true),(133,true),(132,true),(131,true)]
theorem der_106446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106446 :=
  CNF.rup_sound cl_106446 [cl_80635,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80635 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_106448 : CNF.NClause := [(132,true),(18,true),(55,true),(152,true),(140,true),(148,false),(128,false),(151,true),(144,true),(80,false)]
theorem der_106448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106448 :=
  CNF.rup_sound cl_106448 [cl_79050,cl_80957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79050 v h) (hints_cons _ _ _ (der_80957 v h) (by intro d hd; cases hd)))
def cl_106451 : CNF.NClause := [(127,true),(144,false),(146,false),(71,false),(142,true),(133,true),(143,true),(51,true),(150,true),(141,true)]
theorem der_106451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106451 :=
  CNF.rup_sound cl_106451 [cl_81426,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_81426 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_106453 : CNF.NClause := [(914,true),(912,true),(918,true),(901,true),(14,true),(917,true),(909,true),(20,true),(70,true),(923,true)]
theorem der_106453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106453 :=
  CNF.rup_sound cl_106453 [cl_82068,cl_83973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82068 v h) (hints_cons _ _ _ (der_83973 v h) (by intro d hd; cases hd)))
def cl_106454 : CNF.NClause := [(152,false),(86,false),(120,false),(102,false),(64,false),(146,false),(113,false),(111,false),(38,false),(84,false)]
theorem der_106454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106454 :=
  CNF.rup_sound cl_106454 [cl_82264,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82264 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106455 : CNF.NClause := [(152,false),(47,false),(99,false),(97,false),(108,false),(64,false),(120,false),(146,false),(86,false),(84,false)]
theorem der_106455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106455 :=
  CNF.rup_sound cl_106455 [cl_82426,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82426 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106456 : CNF.NClause := [(152,false),(122,false),(64,false),(94,false),(55,false),(146,false),(111,false),(107,false),(86,false),(84,false)]
theorem der_106456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106456 :=
  CNF.rup_sound cl_106456 [cl_82169,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82169 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106461 : CNF.NClause := [(38,false),(144,false),(71,false),(120,false),(83,false),(111,false),(95,false),(86,false),(129,false),(104,false)]
theorem der_106461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106461 :=
  CNF.rup_sound cl_106461 [cl_92709,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92709 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106467 : CNF.NClause := [(88,false),(89,false),(79,false),(85,false),(86,false),(84,false),(143,true),(71,false),(141,true),(142,true)]
theorem der_106467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106467 :=
  CNF.rup_sound cl_106467 [cl_92285,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92285 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106468 : CNF.NClause := [(125,false),(32,true),(143,true),(146,true),(131,true),(145,true),(86,false),(151,true),(129,false),(141,true)]
theorem der_106468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106468 :=
  CNF.rup_sound cl_106468 [cl_87166,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87166 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106469 : CNF.NClause := [(132,false),(152,false),(128,false),(114,false),(116,false),(36,false),(117,false),(70,false),(123,false),(84,false)]
theorem der_106469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106469 :=
  CNF.rup_sound cl_106469 [cl_89277,cl_75861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89277 v h) (hints_cons _ _ _ (der_75861 v h) (by intro d hd; cases hd)))
def cl_106470 : CNF.NClause := [(107,true),(5,false),(148,true),(141,true),(128,false),(151,true),(71,false),(39,false),(132,false),(86,false)]
theorem der_106470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106470 :=
  CNF.rup_sound cl_106470 [cl_89642,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89642 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106471 : CNF.NClause := [(120,false),(93,false),(109,false),(125,false),(58,false),(127,false),(100,false),(85,false),(86,false),(75,false)]
theorem der_106471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106471 :=
  CNF.rup_sound cl_106471 [cl_85645,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85645 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106472 : CNF.NClause := [(102,true),(51,false),(3,false),(131,true),(78,false),(88,false),(144,false),(86,false),(143,true),(150,true)]
theorem der_106472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106472 :=
  CNF.rup_sound cl_106472 [cl_86331,cl_105704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86331 v h) (hints_cons _ _ _ (der_105704 v h) (by intro d hd; cases hd)))
def cl_106473 : CNF.NClause := [(120,false),(93,false),(109,false),(131,true),(58,false),(127,false),(126,false),(79,false),(107,false),(85,false)]
theorem der_106473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106473 :=
  CNF.rup_sound cl_106473 [cl_86036,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86036 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_106474 : CNF.NClause := [(115,false),(120,false),(125,false),(99,false),(108,false),(86,false),(85,false),(47,false),(75,false),(127,false)]
theorem der_106474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106474 :=
  CNF.rup_sound cl_106474 [cl_85588,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85588 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106475 : CNF.NClause := [(20,false),(138,false),(142,true),(88,false),(45,false),(117,true),(125,true),(146,true),(62,false),(83,false)]
theorem der_106475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106475 :=
  CNF.rup_sound cl_106475 [cl_89175,cl_95938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89175 v h) (hints_cons _ _ _ (der_95938 v h) (by intro d hd; cases hd)))
def cl_106476 : CNF.NClause := [(907,true),(903,true),(919,false),(74,true),(916,true),(914,true),(909,true),(905,true),(917,true),(911,true)]
theorem der_106476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106476 :=
  CNF.rup_sound cl_106476 [cl_90887,cl_75161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90887 v h) (hints_cons _ _ _ (der_75161 v h) (by intro d hd; cases hd)))
def cl_106477 : CNF.NClause := [(135,false),(37,false),(126,false),(80,false),(50,false),(64,false),(104,false),(128,false),(132,false),(84,false)]
theorem der_106477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106477 :=
  CNF.rup_sound cl_106477 [cl_95420,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95420 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106478 : CNF.NClause := [(1,false),(59,false),(135,false),(86,false),(109,false),(50,false),(128,false),(71,false),(132,false),(81,false)]
theorem der_106478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106478 :=
  CNF.rup_sound cl_106478 [cl_94880,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94880 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_106479 : CNF.NClause := [(144,false),(109,false),(86,false),(129,false),(35,false),(83,false),(71,false),(104,false),(94,false),(118,false)]
theorem der_106479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106479 :=
  CNF.rup_sound cl_106479 [cl_91809,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91809 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106480 : CNF.NClause := [(102,true),(125,false),(135,false),(50,false),(141,true),(147,true),(150,true),(69,false),(86,false),(144,false)]
theorem der_106480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106480 :=
  CNF.rup_sound cl_106480 [cl_93608,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93608 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106481 : CNF.NClause := [(110,true),(89,false),(39,false),(132,false),(86,false),(128,false),(145,true),(12,false),(126,true),(5,false)]
theorem der_106481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106481 :=
  CNF.rup_sound cl_106481 [cl_90378,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90378 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_106482 : CNF.NClause := [(150,false),(98,false),(130,false),(119,false),(71,false),(104,false),(116,false),(52,false),(79,false),(128,false)]
theorem der_106482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106482 :=
  CNF.rup_sound cl_106482 [cl_90597,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90597 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_106484 : CNF.NClause := [(126,false),(120,false),(84,false),(117,false),(135,false),(128,false),(63,false),(101,false),(45,false),(103,false)]
theorem der_106484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106484 :=
  CNF.rup_sound cl_106484 [cl_94955,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94955 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106486 : CNF.NClause := [(152,false),(135,false),(69,false),(83,false),(84,false),(105,false),(95,false),(118,false),(110,false),(33,false)]
theorem der_106486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106486 :=
  CNF.rup_sound cl_106486 [cl_92697,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92697 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106487 : CNF.NClause := [(45,false),(139,false),(71,false),(49,false),(69,false),(112,false),(78,false),(144,false),(37,false),(38,false)]
theorem der_106487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106487 :=
  CNF.rup_sound cl_106487 [cl_94283,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94283 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106488 : CNF.NClause := [(52,false),(119,false),(104,false),(135,false),(72,false),(83,false),(146,false),(86,false),(110,false),(116,false)]
theorem der_106488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106488 :=
  CNF.rup_sound cl_106488 [cl_90477,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90477 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106489 : CNF.NClause := [(144,false),(52,false),(71,false),(110,false),(104,false),(119,false),(97,false),(129,false),(86,false),(83,false)]
theorem der_106489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106489 :=
  CNF.rup_sound cl_106489 [cl_90254,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90254 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106490 : CNF.NClause := [(93,false),(60,false),(111,false),(117,false),(64,false),(119,false),(126,false),(128,false),(79,false),(84,false)]
theorem der_106490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106490 :=
  CNF.rup_sound cl_106490 [cl_90901,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90901 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_106491 : CNF.NClause := [(32,false),(126,false),(69,false),(128,false),(43,false),(71,false),(37,false),(129,false),(144,false),(86,false)]
theorem der_106491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106491 :=
  CNF.rup_sound cl_106491 [cl_92274,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92274 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106492 : CNF.NClause := [(105,false),(100,false),(33,false),(83,false),(110,false),(148,false),(76,false),(136,false),(128,false),(2,false)]
theorem der_106492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106492 :=
  CNF.rup_sound cl_106492 [cl_95313,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95313 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_106493 : CNF.NClause := [(135,false),(104,false),(146,false),(83,false),(99,false),(118,false),(72,false),(94,false),(35,false),(86,false)]
theorem der_106493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106493 :=
  CNF.rup_sound cl_106493 [cl_92013,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92013 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106494 : CNF.NClause := [(37,false),(55,false),(93,false),(152,false),(43,false),(146,false),(64,false),(104,false),(86,false),(84,false)]
theorem der_106494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106494 :=
  CNF.rup_sound cl_106494 [cl_90952,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90952 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106496 : CNF.NClause := [(126,false),(97,false),(84,false),(128,false),(101,false),(37,false),(122,false),(135,false),(63,false),(113,false)]
theorem der_106496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106496 :=
  CNF.rup_sound cl_106496 [cl_94989,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94989 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106498 : CNF.NClause := [(75,true),(926,true),(900,true),(913,true),(918,true),(916,true),(907,true),(3,true),(903,true),(925,true)]
theorem der_106498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106498 :=
  CNF.rup_sound cl_106498 [cl_93620,cl_93635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93620 v h) (hints_cons _ _ _ (der_93635 v h) (by intro d hd; cases hd)))
def cl_106501 : CNF.NClause := [(110,true),(126,true),(86,false),(145,true),(132,false),(39,false),(10,false),(78,false),(89,false),(150,true)]
theorem der_106501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106501 :=
  CNF.rup_sound cl_106501 [cl_90401,cl_63081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90401 v h) (hints_cons _ _ _ (der_63081 v h) (by intro d hd; cases hd)))
def cl_106502 : CNF.NClause := [(109,true),(58,false),(125,true),(145,false),(147,true),(131,true),(143,true),(78,false),(130,false),(88,false)]
theorem der_106502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106502 :=
  CNF.rup_sound cl_106502 [cl_90419,cl_106104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90419 v h) (hints_cons _ _ _ (der_106104 v h) (by intro d hd; cases hd)))
def cl_106503 : CNF.NClause := [(115,true),(36,false),(151,true),(146,false),(24,false),(153,false),(76,false),(128,false),(86,false),(84,false)]
theorem der_106503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106503 :=
  CNF.rup_sound cl_106503 [cl_90758,cl_63071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90758 v h) (hints_cons _ _ _ (der_63071 v h) (by intro d hd; cases hd)))
def cl_106504 : CNF.NClause := [(148,false),(102,false),(104,false),(38,false),(120,false),(80,false),(130,false),(84,false),(95,false),(128,false)]
theorem der_106504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106504 :=
  CNF.rup_sound cl_106504 [cl_92185,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92185 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_106505 : CNF.NClause := [(152,false),(45,false),(50,false),(128,false),(38,false),(126,false),(63,false),(135,false),(84,false),(79,false)]
theorem der_106505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106505 :=
  CNF.rup_sound cl_106505 [cl_94839,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94839 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106506 : CNF.NClause := [(38,false),(120,false),(111,false),(126,false),(128,false),(83,false),(102,false),(113,false),(84,false),(79,false)]
theorem der_106506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106506 :=
  CNF.rup_sound cl_106506 [cl_95412,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95412 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_106508 : CNF.NClause := [(137,true),(49,true),(152,true),(146,false),(140,true),(141,true),(129,true),(131,true),(86,false),(142,false)]
theorem der_106508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106508 :=
  CNF.rup_sound cl_106508 [cl_100514,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100514 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_106509 : CNF.NClause := [(49,true),(142,false),(129,true),(143,true),(73,false),(128,true),(132,true),(131,true),(77,false),(138,false)]
theorem der_106509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106509 :=
  CNF.rup_sound cl_106509 [cl_97488,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97488 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_106510 : CNF.NClause := [(125,true),(49,true),(69,false),(134,true),(138,false),(140,true),(137,true),(142,false),(77,false),(145,true)]
theorem der_106510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106510 :=
  CNF.rup_sound cl_106510 [cl_98111,cl_86128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98111 v h) (hints_cons _ _ _ (der_86128 v h) (by intro d hd; cases hd)))
def cl_106512 : CNF.NClause := [(101,false),(51,false),(99,false),(100,false),(145,false),(137,false),(123,false),(67,false),(78,false),(79,false)]
theorem der_106512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106512 :=
  CNF.rup_sound cl_106512 [cl_99026,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99026 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106513 : CNF.NClause := [(101,false),(134,false),(139,false),(113,false),(37,false),(97,false),(73,false),(122,false),(79,false),(75,false)]
theorem der_106513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106513 :=
  CNF.rup_sound cl_106513 [cl_99864,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99864 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_106514 : CNF.NClause := [(110,false),(45,false),(120,false),(131,true),(141,true),(101,false),(148,false),(136,false),(63,false),(117,false)]
theorem der_106514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106514 :=
  CNF.rup_sound cl_106514 [cl_96950,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96950 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_106515 : CNF.NClause := [(108,false),(46,false),(133,false),(129,true),(109,false),(153,false),(110,false),(123,false),(131,true),(81,false)]
theorem der_106515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106515 :=
  CNF.rup_sound cl_106515 [cl_100184,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100184 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_106516 : CNF.NClause := [(132,true),(129,false),(135,false),(125,true),(130,true),(140,true),(131,true),(40,true),(63,false),(75,false)]
theorem der_106516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106516 :=
  CNF.rup_sound cl_106516 [cl_97466,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97466 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106517 : CNF.NClause := [(103,false),(95,false),(69,false),(133,false),(43,false),(116,false),(122,false),(153,false),(63,false),(75,false)]
theorem der_106517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106517 :=
  CNF.rup_sound cl_106517 [cl_98756,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98756 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_106518 : CNF.NClause := [(139,false),(129,false),(84,false),(101,false),(94,false),(45,false),(103,false),(120,false),(85,false),(138,false)]
theorem der_106518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106518 :=
  CNF.rup_sound cl_106518 [cl_96384,cl_62455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96384 v h) (hints_cons _ _ _ (der_62455 v h) (by intro d hd; cases hd)))
def cl_106519 : CNF.NClause := [(98,false),(138,false),(51,false),(99,false),(151,false),(123,false),(69,false),(78,false),(85,false),(102,false)]
theorem der_106519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106519 :=
  CNF.rup_sound cl_106519 [cl_99030,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99030 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_106520 : CNF.NClause := [(123,false),(14,false),(46,false),(110,false),(112,false),(68,false),(153,false),(137,false),(108,false),(139,false)]
theorem der_106520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106520 :=
  CNF.rup_sound cl_106520 [cl_99040,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99040 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_106524 : CNF.NClause := [(104,true),(49,false),(135,true),(140,true),(130,false),(88,false),(73,false),(128,false),(85,false),(138,false)]
theorem der_106524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106524 :=
  CNF.rup_sound cl_106524 [cl_101077,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101077 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_106525 : CNF.NClause := [(59,false),(60,false),(42,false),(39,false),(44,false),(136,false),(72,false),(64,false),(130,false),(68,false)]
theorem der_106525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106525 :=
  CNF.rup_sound cl_106525 [cl_95793,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95793 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_106526 : CNF.NClause := [(93,false),(60,false),(111,false),(131,true),(126,false),(99,false),(84,false),(86,false),(119,false),(125,false)]
theorem der_106526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106526 :=
  CNF.rup_sound cl_106526 [cl_95868,cl_105758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95868 v h) (hints_cons _ _ _ (der_105758 v h) (by intro d hd; cases hd)))
def cl_106527 : CNF.NClause := [(123,false),(115,false),(116,false),(135,false),(132,false),(36,false),(117,false),(69,false),(80,false),(72,false)]
theorem der_106527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106527 :=
  CNF.rup_sound cl_106527 [cl_101621,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101621 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_106528 : CNF.NClause := [(112,false),(110,false),(139,false),(138,false),(123,false),(130,false),(46,false),(143,true),(148,false),(141,true)]
theorem der_106528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106528 :=
  CNF.rup_sound cl_106528 [cl_101672,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101672 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_106529 : CNF.NClause := [(137,false),(120,false),(101,false),(110,false),(117,false),(45,false),(133,false),(82,false),(75,false),(63,false)]
theorem der_106529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106529 :=
  CNF.rup_sound cl_106529 [cl_101994,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101994 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106530 : CNF.NClause := [(123,false),(137,false),(146,false),(113,false),(117,false),(36,false),(116,false),(77,false),(70,false),(141,false)]
theorem der_106530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106530 :=
  CNF.rup_sound cl_106530 [cl_102483,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102483 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_106531 : CNF.NClause := [(123,false),(146,false),(51,false),(101,false),(143,false),(15,false),(85,false),(100,false),(99,false),(138,false)]
theorem der_106531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106531 :=
  CNF.rup_sound cl_106531 [cl_102810,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102810 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106536 : CNF.NClause := [(40,false),(60,false),(116,false),(77,false),(151,false),(140,false),(35,false),(85,false),(75,false),(39,false)]
theorem der_106536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106536 :=
  CNF.rup_sound cl_106536 [cl_104641,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104641 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_106537 : CNF.NClause := [(134,false),(114,false),(94,false),(139,false),(118,false),(99,false),(35,false),(75,false),(128,false),(79,false)]
theorem der_106537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106537 :=
  CNF.rup_sound cl_106537 [cl_104702,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104702 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106538 : CNF.NClause := [(148,false),(55,true),(86,false),(143,true),(89,false),(85,false),(141,true),(131,false),(142,true),(79,false)]
theorem der_106538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106538 :=
  CNF.rup_sound cl_106538 [cl_104947,cl_62592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104947 v h) (hints_cons _ _ _ (der_62592 v h) (by intro d hd; cases hd)))
def cl_106541 : CNF.NClause := [(920,false),(77,false),(104,true),(66,false),(35,false),(85,false),(142,false),(65,false),(73,false),(79,false)]
theorem der_106541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106541 :=
  CNF.rup_sound cl_106541 [cl_105200,cl_105706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105200 v h) (hints_cons _ _ _ (der_105706 v h) (by intro d hd; cases hd)))
def cl_106542 : CNF.NClause := [(38,false),(53,false),(148,false),(70,false),(3,false),(75,false),(85,false),(142,false),(128,false),(39,false)]
theorem der_106542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106542 :=
  CNF.rup_sound cl_106542 [cl_105502,cl_105700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105502 v h) (hints_cons _ _ _ (der_105700 v h) (by intro d hd; cases hd)))
def cl_106543 : CNF.NClause := [(127,true),(136,true),(138,true),(143,false),(151,true),(145,true),(141,false),(130,true),(152,true),(51,true)]
theorem der_106543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106543 :=
  CNF.rup_sound cl_106543 [cl_105589,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105589 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106550 : CNF.NClause := [(34,true),(134,true),(127,false),(146,false),(65,false),(131,true),(137,true),(152,true),(17,true),(138,true),(135,true)]
theorem der_106550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106550 :=
  CNF.rup_sound cl_106550 [cl_80650,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80650 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_106551 : CNF.NClause := [(126,false),(33,true),(135,true),(139,true),(134,false),(141,true),(131,true),(132,true),(151,true),(153,true),(84,false)]
theorem der_106551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106551 :=
  CNF.rup_sound cl_106551 [cl_80652,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80652 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106552 : CNF.NClause := [(903,true),(922,true),(904,true),(906,true),(919,false),(74,true),(916,true),(910,true),(912,true),(29,true),(900,true)]
theorem der_106552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106552 :=
  CNF.rup_sound cl_106552 [cl_79081,cl_96302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79081 v h) (hints_cons _ _ _ (der_96302 v h) (by intro d hd; cases hd)))
def cl_106553 : CNF.NClause := [(59,false),(101,false),(151,false),(104,false),(121,false),(112,false),(140,false),(150,true),(84,false),(78,false),(77,false)]
theorem der_106553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106553 :=
  CNF.rup_sound cl_106553 [cl_80654,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80654 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_106555 : CNF.NClause := [(135,true),(143,true),(131,false),(128,true),(137,true),(141,true),(147,true),(134,false),(41,true),(125,true),(73,false)]
theorem der_106555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106555 :=
  CNF.rup_sound cl_106555 [cl_72271,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72271 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106556 : CNF.NClause := [(920,true),(927,true),(33,true),(131,true),(917,true),(909,true),(911,true),(126,false),(921,true),(79,false),(916,true)]
theorem der_106556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106556 :=
  CNF.rup_sound cl_106556 [cl_80657,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80657 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106562 : CNF.NClause := [(914,true),(909,true),(925,true),(911,true),(908,true),(910,true),(903,true),(14,true),(901,true),(70,true),(20,true)]
theorem der_106562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106562 :=
  CNF.rup_sound cl_106562 [cl_82081,cl_83973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82081 v h) (hints_cons _ _ _ (der_83973 v h) (by intro d hd; cases hd)))
def cl_106565 : CNF.NClause := [(137,false),(135,true),(151,true),(133,true),(153,true),(142,true),(143,true),(152,true),(131,true),(128,false),(35,true)]
theorem der_106565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106565 :=
  CNF.rup_sound cl_106565 [cl_79094,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79094 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_106572 : CNF.NClause := [(132,true),(130,false),(152,true),(144,true),(70,false),(74,false),(37,true),(151,false),(66,false),(140,true),(128,true)]
theorem der_106572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106572 :=
  CNF.rup_sound cl_106572 [cl_84952,cl_57205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84952 v h) (hints_cons _ _ _ (der_57205 v h) (by intro d hd; cases hd)))
def cl_106574 : CNF.NClause := [(133,true),(148,true),(130,false),(139,false),(125,true),(141,true),(78,false),(77,false),(151,true),(46,true),(131,true)]
theorem der_106574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106574 :=
  CNF.rup_sound cl_106574 [cl_86650,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86650 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106575 : CNF.NClause := [(103,false),(144,false),(129,false),(68,false),(44,false),(109,false),(67,false),(86,false),(119,false),(71,false),(96,false)]
theorem der_106575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106575 :=
  CNF.rup_sound cl_106575 [cl_85983,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85983 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106576 : CNF.NClause := [(117,false),(139,false),(120,false),(71,false),(70,false),(144,false),(94,false),(151,false),(68,false),(45,false),(103,false)]
theorem der_106576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106576 :=
  CNF.rup_sound cl_106576 [cl_86189,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86189 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106577 : CNF.NClause := [(108,false),(126,false),(71,false),(125,false),(49,false),(131,true),(122,false),(104,false),(86,false),(84,false),(96,false)]
theorem der_106577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106577 :=
  CNF.rup_sound cl_106577 [cl_86884,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86884 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106580 : CNF.NClause := [(59,false),(86,false),(52,false),(129,false),(144,false),(67,false),(44,false),(39,false),(68,false),(71,false),(42,false)]
theorem der_106580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106580 :=
  CNF.rup_sound cl_106580 [cl_88719,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88719 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106581 : CNF.NClause := [(123,false),(36,false),(126,false),(113,false),(116,false),(114,false),(125,false),(131,true),(86,false),(71,false),(84,false)]
theorem der_106581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106581 :=
  CNF.rup_sound cl_106581 [cl_86714,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86714 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106582 : CNF.NClause := [(101,false),(123,false),(71,false),(88,false),(51,false),(100,false),(153,false),(152,true),(151,true),(91,false),(98,false)]
theorem der_106582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106582 :=
  CNF.rup_sound cl_106582 [cl_86954,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86954 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_106583 : CNF.NClause := [(115,false),(135,false),(122,false),(83,false),(86,false),(55,false),(72,false),(80,false),(94,false),(146,false),(107,false)]
theorem der_106583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106583 :=
  CNF.rup_sound cl_106583 [cl_86029,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86029 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106584 : CNF.NClause := [(103,false),(126,false),(84,false),(104,false),(131,true),(41,false),(123,false),(125,false),(86,false),(106,false),(71,false)]
theorem der_106584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106584 :=
  CNF.rup_sound cl_106584 [cl_86902,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86902 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106585 : CNF.NClause := [(93,false),(127,false),(131,true),(59,false),(104,false),(74,false),(126,false),(112,false),(79,false),(121,false),(85,false)]
theorem der_106585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106585 :=
  CNF.rup_sound cl_106585 [cl_87666,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87666 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_106586 : CNF.NClause := [(100,false),(122,false),(82,false),(96,false),(104,false),(139,false),(129,false),(49,false),(18,false),(86,false),(85,false)]
theorem der_106586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106586 :=
  CNF.rup_sound cl_106586 [cl_85283,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85283 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_106587 : CNF.NClause := [(134,false),(114,false),(128,false),(99,false),(118,false),(139,false),(74,false),(35,false),(94,false),(79,false),(75,false)]
theorem der_106587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106587 :=
  CNF.rup_sound cl_106587 [cl_89859,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89859 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106589 : CNF.NClause := [(113,false),(121,false),(126,false),(84,false),(39,false),(71,false),(125,false),(96,false),(99,false),(131,true),(86,false)]
theorem der_106589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106589 :=
  CNF.rup_sound cl_106589 [cl_86720,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86720 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106591 : CNF.NClause := [(93,false),(120,false),(58,false),(126,false),(127,false),(131,true),(109,false),(79,false),(107,false),(85,false),(75,false)]
theorem der_106591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106591 :=
  CNF.rup_sound cl_106591 [cl_85942,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85942 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106593 : CNF.NClause := [(97,false),(13,false),(130,true),(131,true),(132,false),(102,false),(129,true),(81,false),(118,false),(32,false),(146,false)]
theorem der_106593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106593 :=
  CNF.rup_sound cl_106593 [cl_86686,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86686 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_106595 : CNF.NClause := [(89,false),(132,false),(88,false),(86,false),(143,true),(141,true),(142,true),(75,false),(84,false),(71,false),(85,false)]
theorem der_106595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106595 :=
  CNF.rup_sound cl_106595 [cl_90411,cl_63081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90411 v h) (hints_cons _ _ _ (der_63081 v h) (by intro d hd; cases hd)))
def cl_106597 : CNF.NClause := [(132,false),(126,true),(151,true),(145,true),(152,true),(153,true),(131,true),(142,true),(128,false),(46,true),(138,true)]
theorem der_106597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106597 :=
  CNF.rup_sound cl_106597 [cl_90175,cl_63081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90175 v h) (hints_cons _ _ _ (der_63081 v h) (by intro d hd; cases hd)))
def cl_106598 : CNF.NClause := [(152,false),(105,false),(73,false),(100,false),(76,false),(95,false),(118,false),(132,false),(70,false),(33,false),(84,false)]
theorem der_106598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106598 :=
  CNF.rup_sound cl_106598 [cl_93874,cl_75861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93874 v h) (hints_cons _ _ _ (der_75861 v h) (by intro d hd; cases hd)))
def cl_106599 : CNF.NClause := [(97,false),(129,false),(86,false),(122,false),(101,false),(139,false),(84,false),(85,false),(105,false),(37,false),(79,false)]
theorem der_106599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106599 :=
  CNF.rup_sound cl_106599 [cl_94851,cl_62455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94851 v h) (hints_cons _ _ _ (der_62455 v h) (by intro d hd; cases hd)))
def cl_106600 : CNF.NClause := [(93,false),(127,false),(84,false),(59,false),(121,false),(64,false),(126,false),(112,false),(79,false),(104,false),(85,false)]
theorem der_106600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106600 :=
  CNF.rup_sound cl_106600 [cl_92446,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92446 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_106601 : CNF.NClause := [(28,false),(145,true),(37,false),(72,false),(141,true),(130,false),(97,true),(83,false),(89,false),(125,true),(69,false)]
theorem der_106601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106601 :=
  CNF.rup_sound cl_106601 [cl_91688,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91688 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106605 : CNF.NClause := [(6,false),(108,false),(121,false),(141,true),(50,false),(131,true),(125,false),(94,false),(85,false),(126,false),(146,true)]
theorem der_106605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106605 :=
  CNF.rup_sound cl_106605 [cl_95093,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95093 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_106606 : CNF.NClause := [(139,false),(129,false),(59,false),(86,false),(93,false),(101,false),(84,false),(85,false),(82,false),(104,false),(121,false)]
theorem der_106606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106606 :=
  CNF.rup_sound cl_106606 [cl_94693,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94693 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106607 : CNF.NClause := [(105,false),(144,false),(67,false),(121,false),(94,false),(50,false),(68,false),(139,false),(71,false),(116,false),(79,false)]
theorem der_106607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106607 :=
  CNF.rup_sound cl_106607 [cl_95110,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95110 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106610 : CNF.NClause := [(89,false),(136,true),(141,true),(71,false),(131,false),(86,false),(79,false),(143,true),(84,false),(142,true),(85,false)]
theorem der_106610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106610 :=
  CNF.rup_sound cl_106610 [cl_93302,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93302 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106612 : CNF.NClause := [(144,false),(111,false),(96,false),(34,false),(86,false),(70,false),(71,false),(118,false),(128,false),(129,false),(106,false)]
theorem der_106612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106612 :=
  CNF.rup_sound cl_106612 [cl_90275,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90275 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106613 : CNF.NClause := [(97,true),(37,false),(72,false),(130,false),(22,false),(141,true),(83,false),(125,true),(69,false),(89,false),(145,true)]
theorem der_106613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106613 :=
  CNF.rup_sound cl_106613 [cl_91531,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91531 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_106615 : CNF.NClause := [(126,false),(33,true),(84,false),(135,true),(144,false),(131,true),(129,true),(147,true),(141,true),(137,true),(143,true)]
theorem der_106615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106615 :=
  CNF.rup_sound cl_106615 [cl_97512,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97512 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106616 : CNF.NClause := [(108,false),(105,false),(94,false),(137,false),(121,false),(67,false),(73,false),(145,false),(50,false),(85,false),(79,false)]
theorem der_106616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106616 :=
  CNF.rup_sound cl_106616 [cl_98606,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98606 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106617 : CNF.NClause := [(21,false),(135,false),(130,true),(139,false),(129,true),(104,false),(133,false),(35,false),(131,true),(118,false),(109,false)]
theorem der_106617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106617 :=
  CNF.rup_sound cl_106617 [cl_100089,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100089 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106618 : CNF.NClause := [(101,false),(137,false),(120,false),(45,false),(73,false),(145,false),(94,false),(67,false),(117,false),(85,false),(79,false)]
theorem der_106618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106618 :=
  CNF.rup_sound cl_106618 [cl_96477,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96477 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106619 : CNF.NClause := [(117,false),(135,false),(74,false),(138,false),(142,false),(122,false),(134,false),(49,false),(139,false),(132,false),(75,false)]
theorem der_106619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106619 :=
  CNF.rup_sound cl_106619 [cl_99905,cl_105702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99905 v h) (hints_cons _ _ _ (der_105702 v h) (by intro d hd; cases hd)))
def cl_106620 : CNF.NClause := [(143,false),(135,false),(104,false),(122,false),(117,false),(96,false),(77,false),(49,false),(69,false),(85,false),(72,false)]
theorem der_106620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106620 :=
  CNF.rup_sound cl_106620 [cl_99773,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99773 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106621 : CNF.NClause := [(127,false),(138,false),(80,false),(103,false),(45,false),(117,false),(120,false),(128,false),(83,false),(85,false),(110,false)]
theorem der_106621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106621 :=
  CNF.rup_sound cl_106621 [cl_100983,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100983 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_106622 : CNF.NClause := [(103,false),(43,false),(127,false),(122,false),(112,false),(99,false),(126,false),(84,false),(85,false),(79,false),(75,false)]
theorem der_106622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106622 :=
  CNF.rup_sound cl_106622 [cl_98828,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98828 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_106623 : CNF.NClause := [(103,false),(97,false),(127,false),(42,false),(121,false),(128,false),(100,false),(83,false),(80,false),(85,false),(138,false)]
theorem der_106623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106623 :=
  CNF.rup_sound cl_106623 [cl_98138,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98138 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_106624 : CNF.NClause := [(117,false),(100,false),(122,false),(96,false),(134,false),(49,false),(74,false),(73,false),(139,false),(79,false),(75,false)]
theorem der_106624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106624 :=
  CNF.rup_sound cl_106624 [cl_99993,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99993 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106625 : CNF.NClause := [(113,false),(151,false),(152,true),(121,false),(150,true),(74,false),(80,false),(76,false),(137,false),(39,false),(138,false)]
theorem der_106625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106625 :=
  CNF.rup_sound cl_106625 [cl_98935,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98935 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_106628 : CNF.NClause := [(115,false),(98,false),(134,false),(122,false),(74,false),(139,false),(94,false),(55,false),(73,false),(79,false),(75,false)]
theorem der_106628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106628 :=
  CNF.rup_sound cl_106628 [cl_99980,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99980 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106629 : CNF.NClause := [(51,false),(138,false),(47,false),(65,false),(41,false),(125,false),(74,false),(23,false),(67,false),(81,false),(128,false)]
theorem der_106629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106629 :=
  CNF.rup_sound cl_106629 [cl_97118,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97118 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106630 : CNF.NClause := [(93,false),(125,false),(57,false),(110,false),(122,false),(114,false),(138,false),(80,false),(85,false),(127,false),(75,false)]
theorem der_106630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106630 :=
  CNF.rup_sound cl_106630 [cl_98345,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98345 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106631 : CNF.NClause := [(42,true),(95,false),(43,false),(99,false),(65,false),(122,false),(74,false),(138,false),(116,false),(81,false),(147,false)]
theorem der_106631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106631 :=
  CNF.rup_sound cl_106631 [cl_98397,cl_88565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98397 v h) (hints_cons _ _ _ (der_88565 v h) (by intro d hd; cases hd)))
def cl_106634 : CNF.NClause := [(102,false),(50,false),(94,false),(139,false),(76,false),(134,false),(74,false),(73,false),(116,false),(121,false),(75,false)]
theorem der_106634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106634 :=
  CNF.rup_sound cl_106634 [cl_96440,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96440 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106636 : CNF.NClause := [(120,false),(58,false),(100,false),(73,false),(93,false),(116,false),(74,false),(134,false),(139,false),(79,false),(75,false)]
theorem der_106636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106636 :=
  CNF.rup_sound cl_106636 [cl_97740,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97740 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106638 : CNF.NClause := [(98,false),(55,false),(138,false),(94,false),(76,false),(126,false),(122,false),(111,false),(64,false),(69,false),(125,false)]
theorem der_106638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106638 :=
  CNF.rup_sound cl_106638 [cl_101819,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101819 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_106639 : CNF.NClause := [(105,true),(60,false),(153,false),(3,false),(130,true),(73,false),(131,true),(15,false),(143,true),(75,false),(147,true)]
theorem der_106639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106639 :=
  CNF.rup_sound cl_106639 [cl_102197,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102197 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_106640 : CNF.NClause := [(153,false),(145,false),(53,false),(121,false),(109,false),(136,false),(152,true),(141,true),(71,false),(79,false),(151,true)]
theorem der_106640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106640 :=
  CNF.rup_sound cl_106640 [cl_102292,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102292 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_106641 : CNF.NClause := [(38,false),(145,false),(95,false),(69,false),(133,false),(138,false),(73,false),(120,false),(111,false),(75,false),(102,false)]
theorem der_106641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106641 :=
  CNF.rup_sound cl_106641 [cl_102462,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102462 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106642 : CNF.NClause := [(101,false),(108,false),(48,false),(107,false),(89,false),(132,true),(127,true),(142,true),(88,false),(137,false),(95,false)]
theorem der_106642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106642 :=
  CNF.rup_sound cl_106642 [cl_102635,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102635 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106643 : CNF.NClause := [(133,false),(82,false),(141,false),(109,false),(117,false),(121,false),(53,false),(98,false),(77,false),(70,false),(64,false)]
theorem der_106643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106643 :=
  CNF.rup_sound cl_106643 [cl_102706,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102706 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_106644 : CNF.NClause := [(123,false),(145,false),(141,false),(111,false),(83,false),(109,false),(46,false),(112,false),(77,false),(138,false),(64,false)]
theorem der_106644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106644 :=
  CNF.rup_sound cl_106644 [cl_102940,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102940 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106646 : CNF.NClause := [(23,false),(1061,true),(83,true),(1060,true),(1055,true),(1056,false),(1064,true),(1074,true),(1083,true),(1067,true),(1071,true)]
theorem der_106646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106646 :=
  CNF.rup_sound cl_106646 [cl_103886,cl_79666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103886 v h) (hints_cons _ _ _ (der_79666 v h) (by intro d hd; cases hd)))
def cl_106648 : CNF.NClause := [(145,false),(121,false),(133,false),(81,false),(129,true),(107,false),(99,false),(131,true),(96,false),(73,false),(39,false)]
theorem der_106648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106648 :=
  CNF.rup_sound cl_106648 [cl_104922,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104922 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106649 : CNF.NClause := [(125,true),(144,false),(126,true),(141,false),(145,true),(150,true),(70,false),(151,true),(148,true),(138,true),(51,true)]
theorem der_106649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106649 :=
  CNF.rup_sound cl_106649 [cl_104975,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104975 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_106650 : CNF.NClause := [(26,false),(145,false),(69,false),(94,true),(138,true),(35,false),(75,false),(80,false),(82,false),(90,false),(128,false)]
theorem der_106650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106650 :=
  CNF.rup_sound cl_106650 [cl_105039,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105039 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106653 : CNF.NClause := [(23,true),(21,true),(53,false),(75,false),(76,false),(64,false),(20,true),(63,false),(91,false),(84,false),(80,false),(55,true)]
theorem der_106653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106653 :=
  CNF.rup_sound cl_106653 [cl_80664,cl_80152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80664 v h) (hints_cons _ _ _ (der_80152 v h) (by intro d hd; cases hd)))
def cl_106658 : CNF.NClause := [(44,false),(6,false),(16,false),(48,false),(43,false),(151,false),(40,false),(60,false),(77,false),(3,false),(68,false),(84,false)]
theorem der_106658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106658 :=
  CNF.rup_sound cl_106658 [cl_80672,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80672 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_106660 : CNF.NClause := [(86,false),(1,false),(76,false),(108,false),(81,false),(48,false),(128,false),(119,false),(95,false),(71,false),(66,false),(101,false)]
theorem der_106660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106660 :=
  CNF.rup_sound cl_106660 [cl_80674,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80674 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_106662 : CNF.NClause := [(93,false),(60,false),(119,false),(69,false),(111,false),(128,false),(131,true),(117,false),(126,false),(83,false),(79,false),(74,false)]
theorem der_106662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106662 :=
  CNF.rup_sound cl_106662 [cl_80676,cl_62171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80676 v h) (hints_cons _ _ _ (der_62171 v h) (by intro d hd; cases hd)))
def cl_106663 : CNF.NClause := [(144,false),(129,false),(119,false),(83,false),(95,false),(84,false),(108,false),(70,false),(48,false),(107,false),(85,false),(86,false)]
theorem der_106663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106663 :=
  CNF.rup_sound cl_106663 [cl_80677,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80677 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_106664 : CNF.NClause := [(98,false),(111,false),(141,true),(122,false),(78,false),(94,false),(55,false),(75,false),(84,false),(68,false),(151,false),(140,false)]
theorem der_106664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106664 :=
  CNF.rup_sound cl_106664 [cl_80679,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80679 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_106665 : CNF.NClause := [(103,false),(119,false),(84,false),(74,false),(128,false),(44,false),(64,false),(102,false),(96,false),(2,false),(79,false),(69,false)]
theorem der_106665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106665 :=
  CNF.rup_sound cl_106665 [cl_79130,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79130 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_106666 : CNF.NClause := [(12,false),(130,false),(100,false),(72,false),(64,false),(81,false),(93,false),(58,false),(68,false),(85,false),(120,false),(107,false)]
theorem der_106666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106666 :=
  CNF.rup_sound cl_106666 [cl_80680,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80680 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_106668 : CNF.NClause := [(134,false),(109,false),(94,false),(82,false),(84,false),(146,false),(35,false),(118,false),(5,false),(99,false),(83,false),(85,false)]
theorem der_106668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106668 :=
  CNF.rup_sound cl_106668 [cl_80681,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80681 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_106673 : CNF.NClause := [(127,true),(143,true),(138,false),(41,true),(145,false),(74,false),(151,true),(135,true),(76,false),(137,true),(75,false),(136,true)]
theorem der_106673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106673 :=
  CNF.rup_sound cl_106673 [cl_76165,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76165 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_106681 : CNF.NClause := [(144,false),(38,false),(104,false),(120,false),(67,false),(70,false),(71,false),(83,false),(95,false),(86,false),(111,false),(129,false)]
theorem der_106681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106681 :=
  CNF.rup_sound cl_106681 [cl_80966,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80966 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106682 : CNF.NClause := [(44,false),(102,false),(64,false),(68,false),(85,false),(130,false),(96,false),(119,false),(72,false),(152,false),(115,false),(12,false)]
theorem der_106682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106682 :=
  CNF.rup_sound cl_106682 [cl_75976,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75976 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_106684 : CNF.NClause := [(28,false),(98,false),(73,false),(132,false),(81,false),(94,false),(55,false),(122,false),(70,false),(29,false),(111,false),(84,false)]
theorem der_106684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106684 :=
  CNF.rup_sound cl_106684 [cl_87341,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87341 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_106690 : CNF.NClause := [(59,false),(93,false),(144,false),(104,false),(67,false),(121,false),(112,false),(86,false),(70,false),(83,false),(129,false),(71,false)]
theorem der_106690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106690 :=
  CNF.rup_sound cl_106690 [cl_84266,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84266 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106696 : CNF.NClause := [(129,false),(104,false),(99,false),(78,false),(35,false),(139,false),(85,false),(84,false),(86,false),(79,false),(118,false),(94,false)]
theorem der_106696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106696 :=
  CNF.rup_sound cl_106696 [cl_89811,cl_62455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89811 v h) (hints_cons _ _ _ (der_62455 v h) (by intro d hd; cases hd)))
def cl_106697 : CNF.NClause := [(132,false),(128,true),(152,true),(55,true),(63,false),(84,false),(144,true),(67,false),(151,true),(24,false),(140,true),(80,false)]
theorem der_106697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106697 :=
  CNF.rup_sound cl_106697 [cl_87082,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_87082 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_106699 : CNF.NClause := [(59,false),(144,false),(129,false),(68,false),(98,false),(83,false),(39,false),(86,false),(42,false),(67,false),(38,false),(71,false)]
theorem der_106699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106699 :=
  CNF.rup_sound cl_106699 [cl_84247,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84247 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106701 : CNF.NClause := [(123,false),(108,false),(71,false),(125,false),(70,false),(110,false),(127,false),(80,false),(85,false),(109,false),(75,false),(46,false)]
theorem der_106701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106701 :=
  CNF.rup_sound cl_106701 [cl_86641,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86641 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_106703 : CNF.NClause := [(59,false),(117,false),(4,false),(78,false),(125,false),(83,false),(73,false),(50,false),(68,false),(42,false),(63,false),(39,false)]
theorem der_106703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106703 :=
  CNF.rup_sound cl_106703 [cl_95462,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95462 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_106704 : CNF.NClause := [(125,false),(139,false),(122,false),(113,false),(37,false),(143,true),(97,false),(101,false),(150,true),(131,true),(13,false),(153,false)]
theorem der_106704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106704 :=
  CNF.rup_sound cl_106704 [cl_95161,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95161 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_106706 : CNF.NClause := [(41,false),(103,false),(126,false),(104,false),(69,false),(84,false),(123,false),(107,false),(79,false),(75,false),(127,false),(85,false)]
theorem der_106706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106706 :=
  CNF.rup_sound cl_106706 [cl_93537,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93537 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_106709 : CNF.NClause := [(109,false),(152,false),(143,false),(84,false),(58,false),(141,true),(107,false),(63,false),(74,false),(142,true),(120,false),(100,false)]
theorem der_106709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106709 :=
  CNF.rup_sound cl_106709 [cl_93896,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93896 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106710 : CNF.NClause := [(111,false),(93,false),(142,false),(85,false),(73,false),(136,false),(81,false),(64,false),(105,false),(60,false),(119,false),(77,false)]
theorem der_106710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106710 :=
  CNF.rup_sound cl_106710 [cl_95327,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95327 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_106711 : CNF.NClause := [(130,false),(24,false),(128,false),(110,false),(76,false),(116,false),(119,false),(67,false),(104,false),(52,false),(80,false),(84,false)]
theorem der_106711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106711 :=
  CNF.rup_sound cl_106711 [cl_90512,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90512 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_106712 : CNF.NClause := [(59,false),(93,false),(82,false),(104,false),(64,false),(74,false),(72,false),(81,false),(121,false),(136,false),(130,false),(115,false)]
theorem der_106712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106712 :=
  CNF.rup_sound cl_106712 [cl_95343,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95343 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_106714 : CNF.NClause := [(28,false),(103,false),(95,false),(70,false),(62,false),(116,false),(43,false),(122,false),(132,false),(81,false),(73,false),(84,false)]
theorem der_106714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106714 :=
  CNF.rup_sound cl_106714 [cl_93353,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93353 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_106715 : CNF.NClause := [(38,false),(111,false),(89,false),(71,false),(83,false),(95,false),(69,false),(86,false),(144,false),(147,false),(104,false),(129,false)]
theorem der_106715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106715 :=
  CNF.rup_sound cl_106715 [cl_91429,cl_88574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91429 v h) (hints_cons _ _ _ (der_88574 v h) (by intro d hd; cases hd)))
def cl_106718 : CNF.NClause := [(28,false),(45,false),(58,false),(73,false),(32,false),(38,false),(132,false),(62,false),(70,false),(33,false),(81,false),(84,false)]
theorem der_106718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106718 :=
  CNF.rup_sound cl_106718 [cl_93345,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93345 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_106719 : CNF.NClause := [(120,false),(93,false),(73,false),(100,false),(107,false),(66,false),(67,false),(58,false),(21,false),(85,false),(137,false),(79,false)]
theorem der_106719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106719 :=
  CNF.rup_sound cl_106719 [cl_95251,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95251 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106720 : CNF.NClause := [(134,false),(109,false),(82,false),(99,false),(128,false),(118,false),(84,false),(5,false),(35,false),(94,false),(86,false),(85,false)]
theorem der_106720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106720 :=
  CNF.rup_sound cl_106720 [cl_90246,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90246 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_106721 : CNF.NClause := [(123,false),(51,false),(101,false),(73,false),(85,false),(66,false),(67,false),(100,false),(99,false),(21,false),(137,false),(79,false)]
theorem der_106721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106721 :=
  CNF.rup_sound cl_106721 [cl_95032,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95032 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106722 : CNF.NClause := [(26,false),(109,false),(62,false),(104,false),(94,false),(128,false),(118,false),(136,false),(35,false),(71,false),(79,false),(75,false)]
theorem der_106722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106722 :=
  CNF.rup_sound cl_106722 [cl_91091,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_91091 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_106725 : CNF.NClause := [(1056,true),(1057,true),(1064,true),(1083,true),(1060,true),(1066,true),(1074,true),(1069,true),(1058,true),(1071,true),(63,true),(1063,true)]
theorem der_106725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106725 :=
  CNF.rup_sound cl_106725 [cl_93200,cl_86776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93200 v h) (hints_cons _ _ _ (der_86776 v h) (by intro d hd; cases hd)))
def cl_106726 : CNF.NClause := [(49,false),(152,false),(77,false),(122,false),(19,false),(85,false),(74,false),(63,false),(71,false),(96,false),(117,false),(100,false)]
theorem der_106726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106726 :=
  CNF.rup_sound cl_106726 [cl_93813,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93813 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_106727 : CNF.NClause := [(243,true),(222,true),(235,true),(219,true),(240,true),(223,true),(227,true),(238,true),(7,false),(80,true),(218,true),(232,true)]
theorem der_106727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106727 :=
  CNF.rup_sound cl_106727 [cl_90078,cl_79653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90078 v h) (hints_cons _ _ _ (der_79653 v h) (by intro d hd; cases hd)))
def cl_106733 : CNF.NClause := [(117,true),(136,false),(71,false),(53,false),(132,true),(66,false),(1,false),(21,false),(144,true),(140,true),(76,false),(86,false)]
theorem der_106733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106733 :=
  CNF.rup_sound cl_106733 [cl_97280,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97280 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_106737 : CNF.NClause := [(117,false),(144,false),(141,true),(89,false),(49,false),(139,false),(142,false),(143,true),(104,false),(122,false),(79,false),(147,false)]
theorem der_106737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106737 :=
  CNF.rup_sound cl_106737 [cl_96811,cl_105704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96811 v h) (hints_cons _ _ _ (der_105704 v h) (by intro d hd; cases hd)))
def cl_106738 : CNF.NClause := [(123,false),(46,false),(152,true),(136,false),(141,true),(108,false),(111,false),(64,false),(109,false),(150,false),(85,false),(71,false)]
theorem der_106738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106738 :=
  CNF.rup_sound cl_106738 [cl_101374,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101374 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_106739 : CNF.NClause := [(98,false),(53,false),(152,true),(141,true),(117,false),(71,false),(150,false),(121,false),(136,false),(64,false),(85,false),(109,false)]
theorem der_106739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106739 :=
  CNF.rup_sound cl_106739 [cl_101292,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101292 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_106740 : CNF.NClause := [(123,false),(21,false),(66,false),(73,false),(117,false),(36,false),(67,false),(137,false),(114,false),(113,false),(85,false),(79,false)]
theorem der_106740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106740 :=
  CNF.rup_sound cl_106740 [cl_100637,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100637 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106741 : CNF.NClause := [(55,false),(67,false),(49,false),(66,false),(137,false),(37,false),(85,false),(21,false),(50,false),(43,false),(73,false),(79,false)]
theorem der_106741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106741 :=
  CNF.rup_sound cl_106741 [cl_95799,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95799 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106742 : CNF.NClause := [(137,false),(130,false),(142,false),(152,false),(115,false),(121,false),(151,true),(59,false),(112,false),(84,false),(138,false),(75,false)]
theorem der_106742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106742 :=
  CNF.rup_sound cl_106742 [cl_97849,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97849 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106743 : CNF.NClause := [(131,false),(138,false),(94,false),(117,false),(73,false),(134,false),(78,false),(15,false),(81,false),(77,false),(101,false),(75,false)]
theorem der_106743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106743 :=
  CNF.rup_sound cl_106743 [cl_96408,cl_72318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96408 v h) (hints_cons _ _ _ (der_72318 v h) (by intro d hd; cases hd)))
def cl_106746 : CNF.NClause := [(123,false),(46,false),(138,false),(108,false),(83,false),(110,false),(4,false),(68,false),(73,false),(111,false),(78,false),(125,false)]
theorem der_106746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106746 :=
  CNF.rup_sound cl_106746 [cl_100121,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100121 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106758 : CNF.NClause := [(49,false),(2,false),(50,false),(71,false),(64,false),(125,false),(43,false),(69,false),(37,false),(84,false),(55,false),(79,false)]
theorem der_106758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106758 :=
  CNF.rup_sound cl_106758 [cl_95800,cl_79467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95800 v h) (hints_cons _ _ _ (der_79467 v h) (by intro d hd; cases hd)))
def cl_106761 : CNF.NClause := [(105,false),(102,false),(121,false),(12,false),(142,false),(15,false),(131,false),(68,false),(94,false),(72,false),(85,false),(50,false)]
theorem der_106761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106761 :=
  CNF.rup_sound cl_106761 [cl_95717,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95717 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_106762 : CNF.NClause := [(38,false),(102,false),(128,false),(113,false),(80,false),(3,false),(95,false),(65,false),(120,false),(85,false),(70,false),(75,false)]
theorem der_106762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106762 :=
  CNF.rup_sound cl_106762 [cl_99131,cl_62171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99131 v h) (hints_cons _ _ _ (der_62171 v h) (by intro d hd; cases hd)))
def cl_106763 : CNF.NClause := [(113,false),(89,false),(153,false),(150,true),(39,false),(110,false),(137,false),(121,false),(152,true),(76,false),(78,false),(80,false)]
theorem der_106763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106763 :=
  CNF.rup_sound cl_106763 [cl_98929,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98929 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_106765 : CNF.NClause := [(98,false),(52,false),(138,false),(119,false),(110,false),(3,false),(104,false),(125,false),(80,false),(85,false),(65,false),(75,false)]
theorem der_106765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106765 :=
  CNF.rup_sound cl_106765 [cl_100041,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100041 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106766 : CNF.NClause := [(93,false),(60,false),(99,false),(126,false),(127,false),(84,false),(117,false),(69,false),(119,false),(64,false),(85,false),(75,false)]
theorem der_106766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106766 :=
  CNF.rup_sound cl_106766 [cl_98881,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98881 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106767 : CNF.NClause := [(903,true),(67,true),(908,true),(912,true),(901,true),(923,true),(905,true),(916,true),(914,false),(925,true),(917,true),(904,true)]
theorem der_106767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106767 :=
  CNF.rup_sound cl_106767 [cl_96600,cl_62078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96600 v h) (hints_cons _ _ _ (der_62078 v h) (by intro d hd; cases hd)))
def cl_106769 : CNF.NClause := [(120,false),(44,false),(106,false),(47,false),(125,false),(99,false),(131,true),(86,false),(84,false),(126,false),(81,false),(108,false)]
theorem der_106769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106769 :=
  CNF.rup_sound cl_106769 [cl_103045,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103045 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106770 : CNF.NClause := [(145,false),(125,false),(126,false),(116,false),(81,false),(146,false),(73,false),(53,false),(71,false),(153,false),(79,false),(35,false)]
theorem der_106770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106770 :=
  CNF.rup_sound cl_106770 [cl_103401,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103401 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106771 : CNF.NClause := [(21,true),(67,false),(64,false),(6,true),(66,false),(151,false),(109,true),(35,false),(85,false),(20,true),(75,false),(90,false)]
theorem der_106771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106771 :=
  CNF.rup_sound cl_106771 [cl_104492,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104492 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_106772 : CNF.NClause := [(21,false),(137,false),(148,false),(18,false),(118,false),(114,false),(99,false),(35,false),(85,false),(66,false),(128,false),(79,false)]
theorem der_106772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106772 :=
  CNF.rup_sound cl_106772 [cl_104526,cl_105700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104526 v h) (hints_cons _ _ _ (der_105700 v h) (by intro d hd; cases hd)))
def cl_106773 : CNF.NClause := [(145,false),(137,false),(134,true),(136,true),(94,false),(138,true),(118,false),(99,false),(35,false),(90,false),(128,false),(79,false)]
theorem der_106773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106773 :=
  CNF.rup_sound cl_106773 [cl_105047,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105047 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106775 : CNF.NClause := [(7,false),(125,false),(146,false),(70,false),(3,false),(75,false),(85,false),(64,false),(80,false),(151,false),(128,false),(39,false)]
theorem der_106775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106775 :=
  CNF.rup_sound cl_106775 [cl_105103,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105103 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106776 : CNF.NClause := [(109,false),(94,false),(81,false),(23,false),(74,false),(67,false),(131,false),(118,false),(99,false),(35,false),(65,false),(83,false)]
theorem der_106776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106776 :=
  CNF.rup_sound cl_106776 [cl_105286,cl_95250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105286 v h) (hints_cons _ _ _ (der_95250 v h) (by intro d hd; cases hd)))
def cl_106778 : CNF.NClause := [(150,false),(151,true),(94,false),(139,true),(118,false),(99,false),(35,false),(130,true),(142,false),(152,true),(90,false),(128,false)]
theorem der_106778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106778 :=
  CNF.rup_sound cl_106778 [cl_105605,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105605 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_106781 : CNF.NClause := [(34,true),(33,false),(92,false),(85,false),(110,false),(81,false),(87,false),(105,false),(90,false),(100,false),(115,false),(35,false),(43,false)]
theorem der_106781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106781 :=
  CNF.rup_sound cl_106781 [cl_80689,cl_79727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80689 v h) (hints_cons _ _ _ (der_79727 v h) (by intro d hd; cases hd)))
def cl_106782 : CNF.NClause := [(59,false),(103,false),(101,false),(55,true),(48,false),(44,false),(119,false),(109,false),(43,true),(50,false),(94,false),(121,false),(54,false)]
theorem der_106782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106782 :=
  CNF.rup_sound cl_106782 [cl_80695,cl_64365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80695 v h) (hints_cons _ _ _ (der_64365 v h) (by intro d hd; cases hd)))
def cl_106783 : CNF.NClause := [(92,false),(102,false),(3,false),(119,false),(140,false),(15,false),(96,false),(103,false),(89,false),(79,false),(81,false),(78,false),(44,false)]
theorem der_106783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106783 :=
  CNF.rup_sound cl_106783 [cl_80699,cl_65849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80699 v h) (hints_cons _ _ _ (der_65849 v h) (by intro d hd; cases hd)))
def cl_106785 : CNF.NClause := [(59,false),(48,false),(44,false),(64,false),(151,false),(100,false),(50,false),(54,true),(9,false),(7,false),(71,false),(73,false),(80,false)]
theorem der_106785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106785 :=
  CNF.rup_sound cl_106785 [cl_80704,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80704 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_106786 : CNF.NClause := [(115,false),(98,false),(80,false),(70,false),(128,false),(107,false),(55,false),(3,false),(83,false),(75,false),(122,false),(65,false),(85,false)]
theorem der_106786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106786 :=
  CNF.rup_sound cl_106786 [cl_80706,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80706 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_106787 : CNF.NClause := [(95,false),(119,false),(48,false),(114,false),(141,false),(125,false),(65,false),(3,false),(108,false),(86,false),(75,false),(80,false),(85,false)]
theorem der_106787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106787 :=
  CNF.rup_sound cl_106787 [cl_79161,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79161 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106788 : CNF.NClause := [(134,false),(5,false),(82,false),(99,false),(95,false),(122,false),(84,false),(112,false),(75,false),(43,false),(83,false),(86,false),(85,false)]
theorem der_106788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106788 :=
  CNF.rup_sound cl_106788 [cl_80709,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80709 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_106789 : CNF.NClause := [(102,false),(108,false),(45,true),(116,false),(128,false),(83,false),(50,false),(84,false),(121,false),(131,true),(126,false),(79,false),(74,false)]
theorem der_106789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106789 :=
  CNF.rup_sound cl_106789 [cl_80710,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80710 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_106790 : CNF.NClause := [(45,false),(117,false),(128,false),(3,false),(120,false),(110,false),(63,false),(65,false),(70,false),(75,false),(103,false),(80,false),(85,false)]
theorem der_106790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106790 :=
  CNF.rup_sound cl_106790 [cl_80711,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80711 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_106791 : CNF.NClause := [(95,false),(20,false),(70,false),(53,false),(69,false),(109,false),(71,false),(68,false),(121,false),(86,false),(67,false),(106,false),(129,false)]
theorem der_106791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106791 :=
  CNF.rup_sound cl_106791 [cl_80712,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80712 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_106792 : CNF.NClause := [(20,false),(106,false),(69,false),(67,false),(129,false),(70,false),(34,false),(118,false),(111,false),(71,false),(68,false),(96,false),(86,false)]
theorem der_106792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106792 :=
  CNF.rup_sound cl_106792 [cl_80714,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80714 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_106793 : CNF.NClause := [(119,false),(113,false),(125,false),(131,true),(69,false),(84,false),(126,false),(86,false),(106,false),(74,false),(94,false),(79,false),(40,false)]
theorem der_106793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106793 :=
  CNF.rup_sound cl_106793 [cl_80715,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80715 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106794 : CNF.NClause := [(43,false),(95,false),(78,false),(63,false),(82,false),(9,false),(122,false),(99,false),(81,false),(137,false),(75,false),(116,false),(69,false)]
theorem der_106794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106794 :=
  CNF.rup_sound cl_106794 [cl_80716,cl_76536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80716 v h) (hints_cons _ _ _ (der_76536 v h) (by intro d hd; cases hd)))
def cl_106795 : CNF.NClause := [(115,false),(103,false),(119,false),(80,false),(44,false),(125,false),(109,false),(127,false),(38,true),(86,false),(75,false),(71,false),(85,false)]
theorem der_106795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106795 :=
  CNF.rup_sound cl_106795 [cl_80718,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80718 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_106796 : CNF.NClause := [(130,false),(12,false),(68,false),(81,false),(100,false),(38,true),(115,false),(118,false),(33,false),(72,false),(85,false),(64,false),(110,false)]
theorem der_106796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106796 :=
  CNF.rup_sound cl_106796 [cl_80719,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80719 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_106797 : CNF.NClause := [(98,false),(120,false),(68,false),(4,false),(83,false),(73,false),(105,false),(78,false),(54,false),(112,false),(80,false),(63,false),(127,false)]
theorem der_106797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106797 :=
  CNF.rup_sound cl_106797 [cl_80720,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80720 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_106798 : CNF.NClause := [(136,false),(43,true),(135,true),(139,true),(146,false),(128,true),(143,true),(134,true),(152,true),(141,true),(137,true),(140,true),(129,true)]
theorem der_106798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106798 :=
  CNF.rup_sound cl_106798 [cl_80721,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80721 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_106799 : CNF.NClause := [(115,false),(47,false),(70,false),(146,false),(108,false),(120,false),(80,false),(42,true),(65,false),(99,false),(125,false),(3,false),(85,false)]
theorem der_106799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106799 :=
  CNF.rup_sound cl_106799 [cl_80722,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80722 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106801 : CNF.NClause := [(89,false),(29,false),(119,false),(94,false),(125,false),(146,false),(127,false),(27,false),(113,false),(40,false),(71,false),(78,false),(69,false)]
theorem der_106801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106801 :=
  CNF.rup_sound cl_106801 [cl_80724,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80724 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_106804 : CNF.NClause := [(123,false),(115,false),(36,false),(83,false),(113,false),(73,false),(78,false),(63,false),(68,false),(116,false),(4,false),(125,false),(71,false)]
theorem der_106804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106804 :=
  CNF.rup_sound cl_106804 [cl_80727,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80727 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_106806 : CNF.NClause := [(103,false),(105,false),(41,false),(104,false),(125,false),(71,false),(48,true),(39,true),(127,false),(123,false),(146,false),(85,false),(80,false)]
theorem der_106806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106806 :=
  CNF.rup_sound cl_106806 [cl_80728,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80728 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_106808 : CNF.NClause := [(38,false),(88,false),(113,false),(104,false),(111,false),(23,false),(83,false),(67,false),(137,false),(89,false),(74,false),(95,false),(81,false)]
theorem der_106808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106808 :=
  CNF.rup_sound cl_106808 [cl_81179,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_81179 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_106812 : CNF.NClause := [(113,false),(89,false),(80,false),(96,false),(121,false),(88,false),(153,false),(39,false),(78,false),(110,false),(152,true),(76,false),(150,true)]
theorem der_106812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106812 :=
  CNF.rup_sound cl_106812 [cl_83676,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83676 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_106813 : CNF.NClause := [(18,false),(91,false),(65,false),(131,false),(141,true),(81,false),(37,false),(77,false),(146,true),(122,true),(72,false),(85,false),(86,false)]
theorem der_106813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106813 :=
  CNF.rup_sound cl_106813 [cl_82182,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_82182 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_106816 : CNF.NClause := [(59,false),(93,false),(69,false),(121,false),(129,false),(67,false),(70,false),(104,false),(112,false),(68,false),(20,false),(86,false),(71,false)]
theorem der_106816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106816 :=
  CNF.rup_sound cl_106816 [cl_83065,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83065 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_106817 : CNF.NClause := [(103,false),(20,false),(69,false),(67,false),(71,false),(68,false),(129,false),(86,false),(95,false),(43,false),(112,false),(70,false),(122,false)]
theorem der_106817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106817 :=
  CNF.rup_sound cl_106817 [cl_80975,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80975 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_106818 : CNF.NClause := [(109,false),(134,false),(97,false),(113,false),(37,false),(122,false),(135,true),(71,false),(69,false),(138,true),(144,false),(70,false),(75,false)]
theorem der_106818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106818 :=
  CNF.rup_sound cl_106818 [cl_84108,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84108 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_106819 : CNF.NClause := [(98,false),(55,false),(84,false),(82,false),(83,false),(134,false),(86,false),(94,false),(5,false),(85,false),(111,false),(122,false),(75,false)]
theorem der_106819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106819 :=
  CNF.rup_sound cl_106819 [cl_83364,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83364 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_106821 : CNF.NClause := [(5,false),(134,false),(84,false),(110,false),(120,false),(82,false),(83,false),(94,false),(45,false),(85,false),(75,false),(86,false),(101,false)]
theorem der_106821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106821 :=
  CNF.rup_sound cl_106821 [cl_80943,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80943 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_106824 : CNF.NClause := [(38,false),(20,false),(104,false),(129,false),(111,false),(95,false),(68,false),(71,false),(70,false),(86,false),(69,false),(120,false),(67,false)]
theorem der_106824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106824 :=
  CNF.rup_sound cl_106824 [cl_80947,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80947 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_106829 : CNF.NClause := [(134,false),(109,false),(84,false),(98,false),(95,false),(82,false),(5,false),(86,false),(53,false),(83,false),(85,false),(121,false),(75,false)]
theorem der_106829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106829 :=
  CNF.rup_sound cl_106829 [cl_84454,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84454 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_106831 : CNF.NClause := [(97,false),(115,false),(71,false),(47,false),(120,false),(83,false),(142,false),(26,false),(99,false),(79,false),(86,false),(75,false),(27,false)]
theorem der_106831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106831 :=
  CNF.rup_sound cl_106831 [cl_86237,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86237 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_106832 : CNF.NClause := [(98,false),(53,false),(62,false),(121,false),(26,false),(83,false),(79,false),(130,false),(117,false),(71,false),(78,false),(75,false),(95,false)]
theorem der_106832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106832 :=
  CNF.rup_sound cl_106832 [cl_84458,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84458 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_106834 : CNF.NClause := [(123,false),(51,false),(70,false),(65,false),(98,false),(3,false),(100,false),(80,false),(125,false),(85,false),(86,false),(75,false),(99,false)]
theorem der_106834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106834 :=
  CNF.rup_sound cl_106834 [cl_86863,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86863 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106835 : CNF.NClause := [(38,false),(120,false),(80,false),(3,false),(104,false),(65,false),(95,false),(70,false),(113,false),(85,false),(125,false),(75,false),(71,false)]
theorem der_106835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106835 :=
  CNF.rup_sound cl_106835 [cl_84551,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84551 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_106836 : CNF.NClause := [(123,false),(26,false),(108,false),(75,false),(83,false),(46,false),(148,false),(109,false),(62,false),(79,false),(84,false),(71,false),(112,false)]
theorem der_106836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106836 :=
  CNF.rup_sound cl_106836 [cl_85714,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85714 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_106837 : CNF.NClause := [(26,false),(130,false),(111,false),(74,false),(83,false),(120,false),(79,false),(104,false),(62,false),(71,false),(95,false),(75,false),(38,false)]
theorem der_106837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106837 :=
  CNF.rup_sound cl_106837 [cl_84453,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84453 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_106838 : CNF.NClause := [(123,false),(103,false),(130,false),(41,false),(71,false),(62,false),(74,false),(26,false),(107,false),(104,false),(79,false),(75,false),(83,false)]
theorem der_106838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106838 :=
  CNF.rup_sound cl_106838 [cl_85911,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85911 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_106840 : CNF.NClause := [(113,false),(84,false),(148,false),(121,false),(71,false),(39,false),(80,false),(150,false),(128,false),(96,false),(79,false),(75,false),(99,false)]
theorem der_106840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106840 :=
  CNF.rup_sound cl_106840 [cl_93012,cl_80957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93012 v h) (hints_cons _ _ _ (der_80957 v h) (by intro d hd; cases hd)))
def cl_106844 : CNF.NClause := [(59,false),(86,false),(143,false),(144,false),(77,false),(72,false),(45,false),(129,false),(11,false),(38,false),(69,false),(66,false),(80,false)]
theorem der_106844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106844 :=
  CNF.rup_sound cl_106844 [cl_95317,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95317 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106845 : CNF.NClause := [(89,false),(108,false),(152,true),(137,false),(86,false),(150,true),(80,false),(49,false),(74,false),(122,false),(68,false),(151,false),(104,false)]
theorem der_106845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106845 :=
  CNF.rup_sound cl_106845 [cl_93605,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93605 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_106846 : CNF.NClause := [(98,false),(152,false),(71,false),(84,false),(63,false),(19,false),(77,false),(111,false),(122,false),(85,false),(74,false),(55,false),(107,false)]
theorem der_106846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106846 :=
  CNF.rup_sound cl_106846 [cl_94216,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94216 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106848 : CNF.NClause := [(51,false),(24,false),(38,false),(80,false),(35,false),(67,false),(130,false),(63,false),(78,false),(33,false),(76,false),(41,false),(84,false)]
theorem der_106848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106848 :=
  CNF.rup_sound cl_106848 [cl_92847,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92847 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_106849 : CNF.NClause := [(102,false),(112,false),(135,true),(118,false),(62,false),(80,false),(74,false),(32,false),(29,false),(107,false),(145,false),(68,false),(86,false)]
theorem der_106849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106849 :=
  CNF.rup_sound cl_106849 [cl_93949,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93949 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_106851 : CNF.NClause := [(134,false),(140,false),(128,false),(143,true),(94,false),(118,false),(141,true),(114,false),(35,false),(79,false),(142,true),(75,false),(89,false)]
theorem der_106851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106851 :=
  CNF.rup_sound cl_106851 [cl_92102,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92102 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106854 : CNF.NClause := [(1073,true),(1055,true),(1075,true),(1064,true),(1058,true),(1060,true),(1083,true),(1063,true),(1059,true),(1065,true),(1076,true),(1057,true),(1071,true)]
theorem der_106854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106854 :=
  CNF.rup_sound cl_106854 [cl_92545,cl_15742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92545 v h) (hints_cons _ _ _ (der_15742 v h) (by intro d hd; cases hd)))
def cl_106857 : CNF.NClause := [(113,false),(121,false),(12,false),(39,false),(142,false),(72,false),(107,false),(77,false),(68,false),(85,false),(15,false),(110,false),(64,false)]
theorem der_106857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106857 :=
  CNF.rup_sound cl_106857 [cl_95206,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95206 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_106858 : CNF.NClause := [(102,false),(97,false),(89,false),(65,false),(128,false),(117,false),(74,false),(67,false),(87,false),(23,false),(107,false),(81,false),(32,false)]
theorem der_106858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106858 :=
  CNF.rup_sound cl_106858 [cl_93982,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93982 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_106860 : CNF.NClause := [(59,false),(20,false),(70,false),(39,false),(143,false),(68,false),(129,false),(86,false),(117,false),(85,false),(67,false),(77,false),(135,false)]
theorem der_106860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106860 :=
  CNF.rup_sound cl_106860 [cl_95458,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95458 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106861 : CNF.NClause := [(37,false),(135,false),(72,false),(66,false),(71,false),(77,false),(45,false),(58,false),(85,false),(38,false),(49,false),(143,false),(80,false)]
theorem der_106861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106861 :=
  CNF.rup_sound cl_106861 [cl_95374,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95374 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_106864 : CNF.NClause := [(126,false),(37,false),(42,false),(39,false),(143,true),(76,false),(83,false),(138,true),(128,false),(69,false),(136,false),(84,false),(133,true)]
theorem der_106864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106864 :=
  CNF.rup_sound cl_106864 [cl_95603,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95603 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_106866 : CNF.NClause := [(143,true),(137,true),(132,false),(131,true),(134,true),(49,true),(151,true),(73,false),(144,true),(69,false),(142,false),(86,false),(141,true)]
theorem der_106866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106866 :=
  CNF.rup_sound cl_106866 [cl_97490,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97490 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_106867 : CNF.NClause := [(143,false),(135,false),(69,false),(131,true),(112,false),(85,false),(72,false),(43,false),(128,false),(77,false),(126,false),(122,false),(79,false)]
theorem der_106867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106867 :=
  CNF.rup_sound cl_106867 [cl_95917,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95917 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106871 : CNF.NClause := [(123,false),(136,false),(73,false),(109,false),(15,false),(69,false),(64,false),(142,false),(111,false),(77,false),(110,false),(85,false),(46,false)]
theorem der_106871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106871 :=
  CNF.rup_sound cl_106871 [cl_98428,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98428 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_106872 : CNF.NClause := [(46,false),(123,false),(110,false),(90,false),(131,true),(69,false),(139,false),(135,true),(112,false),(108,false),(137,false),(127,true),(148,true)]
theorem der_106872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106872 :=
  CNF.rup_sound cl_106872 [cl_97718,cl_62596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97718 v h) (hints_cons _ _ _ (der_62596 v h) (by intro d hd; cases hd)))
def cl_106876 : CNF.NClause := [(112,false),(105,false),(148,false),(23,false),(142,false),(120,false),(54,false),(77,false),(65,false),(73,false),(114,false),(84,false),(138,false)]
theorem der_106876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106876 :=
  CNF.rup_sound cl_106876 [cl_101353,cl_105700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101353 v h) (hints_cons _ _ _ (der_105700 v h) (by intro d hd; cases hd)))
def cl_106879 : CNF.NClause := [(88,false),(108,false),(150,true),(143,false),(116,false),(50,false),(121,false),(153,false),(89,false),(144,true),(125,true),(94,false),(78,false)]
theorem der_106879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106879 :=
  CNF.rup_sound cl_106879 [cl_102332,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102332 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106886 : CNF.NClause := [(103,false),(111,false),(145,false),(121,false),(42,false),(133,false),(69,false),(114,false),(75,false),(82,false),(63,false),(73,false),(79,false)]
theorem der_106886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106886 :=
  CNF.rup_sound cl_106886 [cl_105051,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105051 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_106888 : CNF.NClause := [(22,false),(132,true),(128,true),(140,true),(64,false),(141,true),(137,true),(133,true),(136,true),(53,true),(90,false),(86,false),(75,false),(78,false)]
theorem der_106888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106888 :=
  CNF.rup_sound cl_106888 [cl_40830,cl_96718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40830 v h) (hints_cons _ _ _ (der_96718 v h) (by intro d hd; cases hd)))
def cl_106889 : CNF.NClause := [(59,false),(115,false),(71,false),(54,true),(80,false),(93,false),(3,false),(121,false),(70,false),(65,false),(75,false),(104,false),(85,false),(125,false)]
theorem der_106889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106889 :=
  CNF.rup_sound cl_106889 [cl_80748,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80748 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_106890 : CNF.NClause := [(93,false),(10,false),(60,false),(72,false),(76,false),(99,false),(141,true),(119,false),(75,false),(73,false),(79,false),(74,false),(139,false),(117,false)]
theorem der_106890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106890 :=
  CNF.rup_sound cl_106890 [cl_80750,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80750 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_106891 : CNF.NClause := [(40,false),(119,false),(113,false),(86,false),(84,false),(1,false),(71,false),(66,false),(106,false),(126,false),(94,false),(81,false),(131,true),(76,false)]
theorem der_106891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106891 :=
  CNF.rup_sound cl_106891 [cl_80752,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80752 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_106892 : CNF.NClause := [(921,true),(904,true),(917,true),(128,false),(908,true),(916,true),(35,true),(902,true),(926,true),(928,true),(907,true),(927,true),(910,true),(911,true)]
theorem der_106892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106892 :=
  CNF.rup_sound cl_106892 [cl_79229,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79229 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_106896 : CNF.NClause := [(130,false),(102,false),(70,false),(95,false),(104,false),(67,false),(128,false),(84,false),(80,false),(38,false),(24,false),(76,false),(120,false),(74,false)]
theorem der_106896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106896 :=
  CNF.rup_sound cl_106896 [cl_73661,cl_57205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73661 v h) (hints_cons _ _ _ (der_57205 v h) (by intro d hd; cases hd)))
def cl_106900 : CNF.NClause := [(132,true),(35,true),(135,true),(138,true),(152,true),(140,true),(128,false),(141,true),(142,true),(127,true),(150,true),(151,true),(133,false),(143,true)]
theorem der_106900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106900 :=
  CNF.rup_sound cl_106900 [cl_79239,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79239 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_106901 : CNF.NClause := [(40,false),(113,false),(2,false),(74,false),(94,false),(106,false),(125,false),(84,false),(79,false),(119,false),(69,false),(81,false),(64,false),(71,false)]
theorem der_106901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106901 :=
  CNF.rup_sound cl_106901 [cl_84077,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84077 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_106902 : CNF.NClause := [(98,false),(111,false),(69,false),(125,false),(86,false),(94,false),(71,false),(74,false),(55,false),(64,false),(79,false),(2,false),(84,false),(122,false)]
theorem der_106902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106902 :=
  CNF.rup_sound cl_106902 [cl_83372,cl_76529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83372 v h) (hints_cons _ _ _ (der_76529 v h) (by intro d hd; cases hd)))
def cl_106906 : CNF.NClause := [(102,false),(2,false),(64,false),(84,false),(98,false),(123,false),(74,false),(70,false),(79,false),(69,false),(99,false),(127,false),(51,false),(80,false)]
theorem der_106906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106906 :=
  CNF.rup_sound cl_106906 [cl_76047,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76047 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_106908 : CNF.NClause := [(119,false),(102,false),(115,false),(68,false),(109,false),(142,false),(85,false),(81,false),(44,false),(72,false),(73,false),(12,false),(64,false),(77,false)]
theorem der_106908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106908 :=
  CNF.rup_sound cl_106908 [cl_85190,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_85190 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_106910 : CNF.NClause := [(117,false),(2,false),(64,false),(59,false),(71,false),(39,false),(74,false),(42,false),(69,false),(81,false),(125,false),(86,false),(84,false),(102,false)]
theorem der_106910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106910 :=
  CNF.rup_sound cl_106910 [cl_84374,cl_79629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84374 v h) (hints_cons _ _ _ (der_79629 v h) (by intro d hd; cases hd)))
def cl_106917 : CNF.NClause := [(38,false),(120,false),(125,false),(81,false),(2,false),(64,false),(104,false),(69,false),(79,false),(113,false),(74,false),(86,false),(84,false),(111,false)]
theorem der_106917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106917 :=
  CNF.rup_sound cl_106917 [cl_84714,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_84714 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106919 : CNF.NClause := [(152,false),(136,false),(54,false),(42,false),(64,false),(63,false),(69,false),(142,false),(45,false),(71,false),(19,false),(74,false),(85,false),(84,false)]
theorem der_106919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106919 :=
  CNF.rup_sound cl_106919 [cl_95316,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95316 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_106923 : CNF.NClause := [(117,false),(110,false),(120,false),(11,false),(69,false),(80,false),(143,false),(66,false),(45,false),(71,false),(72,false),(101,false),(77,false),(83,false)]
theorem der_106923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106923 :=
  CNF.rup_sound cl_106923 [cl_95016,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95016 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_106924 : CNF.NClause := [(38,false),(120,false),(74,false),(84,false),(125,false),(104,false),(86,false),(2,false),(64,false),(80,false),(132,false),(135,false),(79,false),(69,false)]
theorem der_106924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106924 :=
  CNF.rup_sound cl_106924 [cl_92744,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92744 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_106926 : CNF.NClause := [(38,false),(120,false),(73,false),(134,false),(68,false),(67,false),(144,false),(111,false),(113,false),(72,false),(95,false),(69,false),(71,false),(75,false)]
theorem der_106926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106926 :=
  CNF.rup_sound cl_106926 [cl_93235,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93235 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106930 : CNF.NClause := [(123,false),(115,false),(72,false),(143,false),(69,false),(77,false),(85,false),(117,false),(113,false),(83,false),(11,false),(66,false),(36,false),(80,false)]
theorem der_106930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106930 :=
  CNF.rup_sound cl_106930 [cl_95185,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95185 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_106935 : CNF.NClause := [(72,true),(902,true),(925,true),(905,true),(917,true),(903,true),(914,true),(909,true),(900,true),(912,true),(911,true),(916,true),(920,true),(908,true)]
theorem der_106935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106935 :=
  CNF.rup_sound cl_106935 [cl_93034,cl_15696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93034 v h) (hints_cons _ _ _ (der_15696 v h) (by intro d hd; cases hd)))
def cl_106952 : CNF.NClause := [(928,false),(69,true),(913,true),(926,true),(918,true),(923,true),(911,true),(910,true),(927,true),(18,true),(907,true),(905,true),(915,true),(906,true)]
theorem der_106952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106952 :=
  CNF.rup_sound cl_106952 [cl_99359,cl_15702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99359 v h) (hints_cons _ _ _ (der_15702 v h) (by intro d hd; cases hd)))
def cl_106954 : CNF.NClause := [(12,false),(130,false),(33,false),(38,true),(115,false),(81,false),(132,false),(68,false),(64,false),(135,false),(85,false),(118,false),(72,false),(69,false)]
theorem der_106954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106954 :=
  CNF.rup_sound cl_106954 [cl_96119,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96119 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_106956 : CNF.NClause := [(123,false),(151,false),(89,false),(82,false),(68,false),(152,true),(133,false),(46,false),(150,true),(108,false),(78,false),(80,false),(138,false),(75,false)]
theorem der_106956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106956 :=
  CNF.rup_sound cl_106956 [cl_101668,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101668 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_106957 : CNF.NClause := [(98,false),(146,false),(139,true),(3,false),(121,false),(141,true),(152,true),(150,false),(109,false),(53,false),(151,true),(136,false),(80,false),(147,true)]
theorem der_106957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106957 :=
  CNF.rup_sound cl_106957 [cl_102345,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102345 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_106959 : CNF.NClause := [(140,false),(122,false),(106,false),(139,true),(114,false),(151,false),(57,false),(141,true),(110,false),(85,false),(71,false),(142,true),(90,false),(63,false)]
theorem der_106959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106959 :=
  CNF.rup_sound cl_106959 [cl_104608,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104608 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_106960 : CNF.NClause := [(7,false),(150,false),(151,false),(94,false),(118,false),(35,false),(85,false),(71,false),(136,false),(80,false),(64,false),(82,false),(128,false),(79,false)]
theorem der_106960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106960 :=
  CNF.rup_sound cl_106960 [cl_105059,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105059 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_106961 : CNF.NClause := [(88,false),(109,false),(114,false),(12,false),(138,true),(118,false),(99,false),(35,false),(75,false),(85,false),(142,false),(82,false),(90,false),(128,false)]
theorem der_106961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106961 :=
  CNF.rup_sound cl_106961 [cl_105214,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105214 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_106963 : CNF.NClause := [(67,false),(109,false),(84,false),(24,false),(114,false),(118,false),(99,false),(35,false),(80,false),(142,false),(76,false),(65,false),(63,false),(73,false)]
theorem der_106963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106963 :=
  CNF.rup_sound cl_106963 [cl_105241,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105241 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_106964 : CNF.NClause := [(101,false),(29,false),(34,false),(111,false),(118,false),(81,false),(82,false),(96,false),(76,false),(63,false),(89,false),(78,false),(85,false),(9,false),(27,false)]
theorem der_106964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106964 :=
  CNF.rup_sound cl_106964 [cl_79248,cl_105717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79248 v h) (hints_cons _ _ _ (der_105717 v h) (by intro d hd; cases hd)))
def cl_106966 : CNF.NClause := [(93,false),(119,false),(90,false),(19,false),(54,true),(63,false),(74,false),(132,false),(85,false),(60,false),(111,false),(71,false),(77,false),(68,false),(117,false)]
theorem der_106966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106966 :=
  CNF.rup_sound cl_106966 [cl_80774,cl_60459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80774 v h) (hints_cons _ _ _ (der_60459 v h) (by intro d hd; cases hd)))
def cl_106968 : CNF.NClause := [(53,false),(2,false),(84,false),(123,false),(141,true),(74,false),(69,false),(101,false),(51,false),(125,false),(64,false),(99,false),(71,false),(79,false),(57,true)]
theorem der_106968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106968 :=
  CNF.rup_sound cl_106968 [cl_79256,cl_105743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79256 v h) (hints_cons _ _ _ (der_105743 v h) (by intro d hd; cases hd)))
def cl_106970 : CNF.NClause := [(140,false),(139,true),(141,true),(118,false),(110,false),(74,false),(89,false),(95,false),(142,true),(71,false),(100,false),(33,false),(90,false),(85,false),(63,false)]
theorem der_106970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106970 :=
  CNF.rup_sound cl_106970 [cl_80784,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80784 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_106971 : CNF.NClause := [(20,false),(10,false),(71,false),(95,false),(122,false),(76,false),(43,false),(69,false),(73,false),(116,false),(72,false),(74,false),(112,false),(146,false),(70,false)]
theorem der_106971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106971 :=
  CNF.rup_sound cl_106971 [cl_69775,cl_105802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_69775 v h) (hints_cons _ _ _ (der_105802 v h) (by intro d hd; cases hd)))
def cl_106972 : CNF.NClause := [(120,false),(89,false),(71,false),(49,false),(76,false),(66,false),(1,false),(2,false),(83,false),(53,false),(23,false),(33,false),(86,false),(67,false),(57,false)]
theorem der_106972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106972 :=
  CNF.rup_sound cl_106972 [cl_80789,cl_49772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80789 v h) (hints_cons _ _ _ (der_49772 v h) (by intro d hd; cases hd)))
def cl_106976 : CNF.NClause := [(88,false),(89,false),(55,false),(83,false),(67,false),(81,false),(137,false),(84,false),(23,false),(107,false),(111,false),(122,false),(74,false),(94,false),(78,false)]
theorem der_106976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106976 :=
  CNF.rup_sound cl_106976 [cl_74440,cl_76536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74440 v h) (hints_cons _ _ _ (der_76536 v h) (by intro d hd; cases hd)))
def cl_106978 : CNF.NClause := [(120,false),(47,false),(80,false),(78,false),(67,false),(24,false),(99,false),(108,false),(74,false),(76,false),(6,false),(106,false),(70,false),(66,false),(133,false)]
theorem der_106978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106978 :=
  CNF.rup_sound cl_106978 [cl_70939,cl_105738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_70939 v h) (hints_cons _ _ _ (der_105738 v h) (by intro d hd; cases hd)))
def cl_106982 : CNF.NClause := [(144,false),(15,false),(67,false),(79,false),(80,false),(113,false),(71,false),(68,false),(78,false),(121,false),(81,false),(107,false),(39,false),(96,false),(18,false)]
theorem der_106982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106982 :=
  CNF.rup_sound cl_106982 [cl_83692,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_83692 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106984 : CNF.NClause := [(109,false),(146,false),(81,false),(85,false),(68,false),(83,false),(94,false),(72,false),(150,false),(152,true),(12,false),(35,false),(104,false),(71,false),(118,false)]
theorem der_106984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106984 :=
  CNF.rup_sound cl_106984 [cl_75512,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_75512 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_106985 : CNF.NClause := [(113,false),(100,false),(73,false),(78,false),(119,false),(15,false),(134,false),(72,false),(79,false),(40,false),(77,false),(81,false),(94,false),(75,false),(80,false)]
theorem der_106985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106985 :=
  CNF.rup_sound cl_106985 [cl_81700,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_81700 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106988 : CNF.NClause := [(94,false),(144,false),(45,false),(81,false),(103,false),(70,false),(120,false),(71,false),(117,false),(78,false),(80,false),(15,false),(18,false),(79,false),(68,false)]
theorem der_106988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106988 :=
  CNF.rup_sound cl_106988 [cl_86190,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86190 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_106990 : CNF.NClause := [(33,false),(67,false),(39,false),(35,false),(10,false),(71,false),(74,false),(76,false),(72,false),(45,false),(70,false),(53,false),(20,false),(128,false),(75,false)]
theorem der_106990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106990 :=
  CNF.rup_sound cl_106990 [cl_89214,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89214 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_106994 : CNF.NClause := [(134,false),(143,true),(73,false),(96,false),(89,false),(78,false),(141,true),(39,false),(74,false),(142,true),(121,false),(79,false),(139,false),(75,false),(113,false)]
theorem der_106994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106994 :=
  CNF.rup_sound cl_106994 [cl_92465,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92465 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_106995 : CNF.NClause := [(11,false),(143,false),(43,false),(45,false),(85,false),(142,false),(83,false),(38,false),(77,false),(66,false),(78,false),(72,false),(69,false),(130,false),(80,false)]
theorem der_106995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_106995 :=
  CNF.rup_sound cl_106995 [cl_94960,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94960 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_107001 : CNF.NClause := [(152,false),(122,false),(13,false),(37,false),(97,false),(113,false),(139,false),(131,true),(125,false),(84,false),(90,false),(150,true),(143,true),(79,false),(151,true)]
theorem der_107001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107001 :=
  CNF.rup_sound cl_107001 [cl_95237,cl_88552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95237 v h) (hints_cons _ _ _ (der_88552 v h) (by intro d hd; cases hd)))
def cl_107005 : CNF.NClause := [(49,false),(32,false),(85,false),(43,false),(8,false),(63,false),(82,false),(19,false),(110,false),(74,false),(37,false),(125,false),(68,false),(18,false),(79,false)]
theorem der_107005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107005 :=
  CNF.rup_sound cl_107005 [cl_93880,cl_49807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93880 v h) (hints_cons _ _ _ (der_49807 v h) (by intro d hd; cases hd)))
def cl_107006 : CNF.NClause := [(32,false),(59,false),(42,false),(74,false),(35,false),(63,false),(1,false),(67,false),(54,false),(24,false),(84,false),(80,false),(130,false),(76,false),(78,false)]
theorem der_107006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107006 :=
  CNF.rup_sound cl_107006 [cl_93574,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93574 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_107014 : CNF.NClause := [(6,false),(121,false),(39,false),(80,false),(96,false),(76,false),(74,false),(67,false),(84,false),(148,false),(110,false),(78,false),(99,false),(70,false),(1,false)]
theorem der_107014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107014 :=
  CNF.rup_sound cl_107014 [cl_96204,cl_105751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96204 v h) (hints_cons _ _ _ (der_105751 v h) (by intro d hd; cases hd)))
def cl_107018 : CNF.NClause := [(88,false),(50,false),(138,true),(137,false),(136,true),(121,false),(74,false),(116,false),(135,true),(94,false),(139,false),(75,false),(76,false),(73,false),(79,false)]
theorem der_107018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107018 :=
  CNF.rup_sound cl_107018 [cl_104687,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104687 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_107021 : CNF.NClause := [(6,false),(119,false),(44,false),(102,false),(69,false),(12,false),(109,false),(87,false),(68,false),(81,false),(2,false),(96,false),(42,true),(79,false),(85,false),(72,false)]
theorem der_107021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107021 :=
  CNF.rup_sound cl_107021 [cl_79288,cl_105737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79288 v h) (hints_cons _ _ _ (der_105737 v h) (by intro d hd; cases hd)))
def cl_107022 : CNF.NClause := [(6,false),(10,false),(78,false),(104,false),(98,false),(72,false),(52,false),(66,false),(141,true),(131,true),(110,false),(119,false),(70,false),(136,false),(85,false),(82,false)]
theorem der_107022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107022 :=
  CNF.rup_sound cl_107022 [cl_80816,cl_79631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80816 v h) (hints_cons _ _ _ (der_79631 v h) (by intro d hd; cases hd)))
def cl_107023 : CNF.NClause := [(6,false),(93,false),(69,false),(82,false),(66,false),(5,true),(116,false),(142,false),(107,false),(77,false),(70,false),(120,false),(74,false),(44,true),(78,false),(58,false)]
theorem der_107023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107023 :=
  CNF.rup_sound cl_107023 [cl_79304,cl_86128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79304 v h) (hints_cons _ _ _ (der_86128 v h) (by intro d hd; cases hd)))
def cl_107029 : CNF.NClause := [(59,false),(24,false),(70,false),(76,false),(1,false),(43,false),(32,false),(63,false),(146,false),(39,false),(49,true),(3,false),(106,false),(84,false),(85,false),(91,false)]
theorem der_107029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107029 :=
  CNF.rup_sound cl_107029 [cl_80823,cl_80919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80823 v h) (hints_cons _ _ _ (der_80919 v h) (by intro d hd; cases hd)))
def cl_107032 : CNF.NClause := [(119,false),(103,false),(53,true),(79,false),(83,false),(86,false),(5,false),(102,false),(84,false),(80,false),(96,false),(44,false),(82,false),(85,false),(139,false),(78,false)]
theorem der_107032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107032 :=
  CNF.rup_sound cl_107032 [cl_73781,cl_61659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73781 v h) (hints_cons _ _ _ (der_61659 v h) (by intro d hd; cases hd)))
def cl_107037 : CNF.NClause := [(98,false),(120,false),(75,false),(54,false),(4,false),(142,true),(114,false),(105,false),(88,false),(132,true),(63,false),(68,false),(78,false),(147,false),(112,false),(73,false)]
theorem der_107037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107037 :=
  CNF.rup_sound cl_107037 [cl_90906,cl_88565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90906 v h) (hints_cons _ _ _ (der_88565 v h) (by intro d hd; cases hd)))
def cl_107038 : CNF.NClause := [(117,false),(120,false),(71,false),(45,false),(85,false),(82,false),(74,false),(18,false),(19,false),(76,false),(63,false),(8,false),(103,false),(68,false),(101,false),(79,false)]
theorem der_107038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107038 :=
  CNF.rup_sound cl_107038 [cl_94370,cl_49807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94370 v h) (hints_cons _ _ _ (der_49807 v h) (by intro d hd; cases hd)))
def cl_107044 : CNF.NClause := [(6,false),(112,false),(102,false),(70,false),(32,false),(24,false),(80,false),(1,false),(78,false),(84,false),(67,false),(117,false),(74,false),(82,false),(63,false),(118,false)]
theorem der_107044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107044 :=
  CNF.rup_sound cl_107044 [cl_92649,cl_79636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_92649 v h) (hints_cons _ _ _ (der_79636 v h) (by intro d hd; cases hd)))
def cl_107051 : CNF.NClause := [(120,false),(58,false),(107,false),(116,false),(82,false),(109,false),(133,false),(150,true),(74,false),(29,false),(152,true),(151,false),(68,false),(80,false),(63,false),(86,false)]
theorem der_107051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107051 :=
  CNF.rup_sound cl_107051 [cl_102385,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102385 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107055 : CNF.NClause := [(120,false),(125,false),(153,true),(85,false),(3,false),(70,false),(113,false),(104,false),(75,false),(38,false),(138,true),(129,true),(80,false),(142,true),(90,false),(65,false)]
theorem der_107055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107055 :=
  CNF.rup_sound cl_107055 [cl_104972,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104972 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107058 : CNF.NClause := [(46,false),(108,true),(18,true),(16,true),(74,false),(141,true),(70,false),(85,false),(71,false),(64,false),(76,false),(90,false),(63,false),(83,false),(78,false),(79,false)]
theorem der_107058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107058 :=
  CNF.rup_sound cl_107058 [cl_105147,cl_64219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105147 v h) (hints_cons _ _ _ (der_64219 v h) (by intro d hd; cases hd)))
def cl_107059 : CNF.NClause := [(22,false),(143,true),(148,true),(139,true),(125,true),(138,true),(133,true),(53,true),(137,true),(90,false),(127,true),(64,false),(131,true),(86,false),(75,false),(132,true),(78,false)]
theorem der_107059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107059 :=
  CNF.rup_sound cl_107059 [cl_40421,cl_96718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_40421 v h) (hints_cons _ _ _ (der_96718 v h) (by intro d hd; cases hd)))
def cl_107061 : CNF.NClause := [(101,false),(53,true),(96,false),(111,false),(27,false),(63,false),(88,false),(78,false),(82,false),(81,false),(34,false),(118,false),(89,false),(76,false),(85,false),(9,false),(62,false)]
theorem der_107061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107061 :=
  CNF.rup_sound cl_107061 [cl_79338,cl_105717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79338 v h) (hints_cons _ _ _ (der_105717 v h) (by intro d hd; cases hd)))
def cl_107064 : CNF.NClause := [(59,false),(53,false),(78,false),(64,false),(68,false),(12,false),(6,false),(52,false),(82,false),(54,true),(74,false),(48,true),(99,false),(85,false),(70,false),(44,false),(81,false)]
theorem der_107064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107064 :=
  CNF.rup_sound cl_107064 [cl_80838,cl_105739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80838 v h) (hints_cons _ _ _ (der_105739 v h) (by intro d hd; cases hd)))
def cl_107071 : CNF.NClause := [(28,false),(12,false),(73,false),(135,false),(83,false),(78,false),(58,false),(85,false),(72,false),(81,false),(64,false),(107,false),(130,false),(68,false),(84,false),(62,false),(120,false)]
theorem der_107071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107071 :=
  CNF.rup_sound cl_107071 [cl_93588,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93588 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_107079 : CNF.NClause := [(113,true),(914,true),(922,true),(129,false),(923,true),(925,true),(917,true),(906,true),(913,true),(915,true),(69,false),(86,false),(133,false),(75,false),(85,false),(128,false),(39,false)]
theorem der_107079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107079 :=
  CNF.rup_sound cl_107079 [cl_105149,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105149 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_107080 : CNF.NClause := [(34,true),(110,false),(24,false),(76,false),(41,true),(74,false),(80,false),(23,false),(81,false),(121,false),(89,false),(91,false),(83,false),(63,false),(99,false),(39,false),(84,false),(113,false)]
theorem der_107080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107080 :=
  CNF.rup_sound cl_107080 [cl_37271,cl_80919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37271 v h) (hints_cons _ _ _ (der_80919 v h) (by intro d hd; cases hd)))
def cl_107084 : CNF.NClause := [(102,false),(103,false),(88,false),(137,false),(109,false),(76,false),(70,false),(142,true),(19,false),(87,false),(147,true),(68,false),(69,false),(80,false),(79,false),(85,false),(115,false),(40,false)]
theorem der_107084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107084 :=
  CNF.rup_sound cl_107084 [cl_80866,cl_105771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80866 v h) (hints_cons _ _ _ (der_105771 v h) (by intro d hd; cases hd)))
def cl_107096 : CNF.NClause := [(38,false),(6,false),(78,false),(133,true),(70,false),(76,false),(67,false),(11,false),(126,false),(42,false),(128,false),(138,true),(39,false),(64,false),(80,false),(84,false),(79,false),(143,true)]
theorem der_107096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107096 :=
  CNF.rup_sound cl_107096 [cl_95400,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95400 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_107107 : CNF.NClause := [(50,false),(121,false),(116,false),(129,true),(147,false),(71,false),(153,true),(141,true),(146,false),(94,false),(140,false),(74,false),(3,false),(75,false),(142,true),(45,true),(65,false),(83,false)]
theorem der_107107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107107 :=
  CNF.rup_sound cl_107107 [cl_104837,cl_105726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104837 v h) (hints_cons _ _ _ (der_105726 v h) (by intro d hd; cases hd)))
def cl_107111 : CNF.NClause := [(147,true),(143,true),(128,false),(137,true),(47,false),(144,true),(141,true),(132,true),(151,false),(58,false),(135,true),(152,true),(140,false),(83,false),(50,true),(130,true),(125,true),(131,true),(139,false)]
theorem der_107111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107111 :=
  CNF.rup_sound cl_107111 [cl_80877,cl_15664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80877 v h) (hints_cons _ _ _ (der_15664 v h) (by intro d hd; cases hd)))
def cl_107116 : CNF.NClause := [(41,true),(143,true),(80,false),(138,true),(133,true),(113,false),(76,false),(12,false),(63,false),(39,false),(34,true),(121,false),(126,false),(147,false),(81,false),(84,false),(89,false),(79,false),(128,false)]
theorem der_107116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107116 :=
  CNF.rup_sound cl_107116 [cl_94769,cl_80919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94769 v h) (hints_cons _ _ _ (der_80919 v h) (by intro d hd; cases hd)))
def cl_107146 : CNF.NClause := [(101,false),(10,false),(81,false),(76,false),(83,false),(133,true),(131,false),(111,false),(82,false),(12,false),(92,false),(96,false),(132,true),(86,false),(75,false),(73,false),(84,false),(68,false),(85,false),(34,false),(118,false),(74,false)]
theorem der_107146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107146 :=
  CNF.rup_sound cl_107146 [cl_79421,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79421 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_107153 : CNF.NClause := [(20,false),(133,true),(130,false),(67,false),(142,true),(139,true),(147,true),(42,false),(69,false),(83,false),(136,false),(152,true),(64,false),(84,false),(68,false),(72,false),(138,true),(153,true),(86,false),(2,false),(79,false),(71,false),(146,true)]
theorem der_107153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107153 :=
  CNF.rup_sound cl_107153 [cl_95810,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95810 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107158 : CNF.NClause := [(140,true),(143,true),(134,true),(142,true),(86,false),(153,false),(80,false),(59,false),(43,false),(151,true),(83,false),(130,false),(152,false),(126,false),(84,false),(85,false),(138,true),(42,false),(131,true),(79,false),(146,true),(139,true),(91,false),(133,true)]
theorem der_107158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107158 :=
  CNF.rup_sound cl_107158 [cl_96156,cl_105782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96156 v h) (hints_cons _ _ _ (der_105782 v h) (by intro d hd; cases hd)))
def cl_107181 : CNF.NClause := [(49,false),(18,true)]
theorem der_107181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107181 :=
  CNF.rup_sound cl_107181 [cl_105753,cl_79701,cl_79594,cl_79687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105753 v h) (hints_cons _ _ _ (der_79701 v h) (hints_cons _ _ _ (der_79594 v h) (hints_cons _ _ _ (der_79687 v h) (by intro d hd; cases hd)))))
def cl_107182 : CNF.NClause := [(33,false),(2,true)]
theorem der_107182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107182 :=
  CNF.rup_sound cl_107182 [cl_105754,cl_80924,cl_79968,cl_79953,cl_105752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105754 v h) (hints_cons _ _ _ (der_80924 v h) (hints_cons _ _ _ (der_79968 v h) (hints_cons _ _ _ (der_79953 v h) (hints_cons _ _ _ (der_105752 v h) (by intro d hd; cases hd))))))
def cl_107183 : CNF.NClause := [(86,true),(53,false)]
theorem der_107183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107183 :=
  CNF.rup_sound cl_107183 [cl_105743,cl_79675,cl_48797,cl_15868,cl_29811,cl_15883,cl_29766,cl_15878,cl_49795,cl_15873,cl_15669,cl_49825,cl_15880,cl_76783,cl_15871,cl_42488,cl_15884,cl_76587,cl_15894,cl_43068,cl_15867,cl_12763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105743 v h) (hints_cons _ _ _ (der_79675 v h) (hints_cons _ _ _ (der_48797 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_29811 v h) (hints_cons _ _ _ (der_15883 v h) (hints_cons _ _ _ (der_29766 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_49795 v h) (hints_cons _ _ _ (der_15873 v h) (hints_cons _ _ _ (der_15669 v h) (hints_cons _ _ _ (der_49825 v h) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_76783 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_42488 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_76587 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_43068 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (inp_12763 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_107184 : CNF.NClause := [(78,true),(46,false),(15,true)]
theorem der_107184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107184 :=
  CNF.rup_sound cl_107184 [cl_105914,cl_105915,cl_80322,cl_105897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105914 v h) (hints_cons _ _ _ (der_105915 v h) (hints_cons _ _ _ (der_80322 v h) (hints_cons _ _ _ (der_105897 v h) (by intro d hd; cases hd)))))
def cl_107185 : CNF.NClause := [(84,true),(36,false),(5,true)]
theorem der_107185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107185 :=
  CNF.rup_sound cl_107185 [cl_105839,cl_79515,cl_105829,cl_79516,cl_79766,cl_105831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105839 v h) (hints_cons _ _ _ (der_79515 v h) (hints_cons _ _ _ (der_105829 v h) (hints_cons _ _ _ (der_79516 v h) (hints_cons _ _ _ (der_79766 v h) (hints_cons _ _ _ (der_105831 v h) (by intro d hd; cases hd)))))))
def cl_107186 : CNF.NClause := [(81,false),(54,false),(23,true)]
theorem der_107186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107186 :=
  CNF.rup_sound cl_107186 [cl_79487,cl_79584,cl_105840,cl_77760,cl_80191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79487 v h) (hints_cons _ _ _ (der_79584 v h) (hints_cons _ _ _ (der_105840 v h) (hints_cons _ _ _ (der_77760 v h) (hints_cons _ _ _ (der_80191 v h) (by intro d hd; cases hd))))))
def cl_107187 : CNF.NClause := [(83,false),(54,false),(23,true)]
theorem der_107187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107187 :=
  CNF.rup_sound cl_107187 [cl_107186,cl_79800,cl_105853,cl_105858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107186 v h) (hints_cons _ _ _ (der_79800 v h) (hints_cons _ _ _ (der_105853 v h) (hints_cons _ _ _ (der_105858 v h) (by intro d hd; cases hd)))))
def cl_107188 : CNF.NClause := [(77,false),(78,true),(46,false)]
theorem der_107188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107188 :=
  CNF.rup_sound cl_107188 [cl_79876,cl_107184,cl_105895,cl_77944,cl_79867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79876 v h) (hints_cons _ _ _ (der_107184 v h) (hints_cons _ _ _ (der_105895 v h) (hints_cons _ _ _ (der_77944 v h) (hints_cons _ _ _ (der_79867 v h) (by intro d hd; cases hd))))))
def cl_107189 : CNF.NClause := [(78,false),(80,true),(46,false)]
theorem der_107189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107189 :=
  CNF.rup_sound cl_107189 [cl_105913,cl_105900,cl_105899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105913 v h) (hints_cons _ _ _ (der_105900 v h) (hints_cons _ _ _ (der_105899 v h) (by intro d hd; cases hd))))
def cl_107190 : CNF.NClause := [(78,false),(81,true),(46,false)]
theorem der_107190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107190 :=
  CNF.rup_sound cl_107190 [cl_107189,cl_79540,cl_79873,cl_77921,cl_105910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107189 v h) (hints_cons _ _ _ (der_79540 v h) (hints_cons _ _ _ (der_79873 v h) (hints_cons _ _ _ (der_77921 v h) (hints_cons _ _ _ (der_105910 v h) (by intro d hd; cases hd))))))
def cl_107191 : CNF.NClause := [(75,true),(80,true),(34,false)]
theorem der_107191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107191 :=
  CNF.rup_sound cl_107191 [cl_79898,cl_105927,cl_105765,cl_105930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79898 v h) (hints_cons _ _ _ (der_105927 v h) (hints_cons _ _ _ (der_105765 v h) (hints_cons _ _ _ (der_105930 v h) (by intro d hd; cases hd)))))
def cl_107192 : CNF.NClause := [(70,false),(80,true),(34,false)]
theorem der_107192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107192 :=
  CNF.rup_sound cl_107192 [cl_107191,cl_79893,cl_105935,cl_105934,cl_105933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107191 v h) (hints_cons _ _ _ (der_79893 v h) (hints_cons _ _ _ (der_105935 v h) (hints_cons _ _ _ (der_105934 v h) (hints_cons _ _ _ (der_105933 v h) (by intro d hd; cases hd))))))
def cl_107193 : CNF.NClause := [(85,false),(75,true),(34,false)]
theorem der_107193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107193 :=
  CNF.rup_sound cl_107193 [cl_105937,cl_107191,cl_105775,cl_29848,cl_15874,cl_49758,cl_15884,cl_49949,cl_15891,cl_49972,cl_15882,cl_40899,cl_15876,cl_44586,cl_15875,cl_76635,cl_15888,cl_12701,cl_49766,cl_15879,cl_49831,cl_15889,cl_15670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105937 v h) (hints_cons _ _ _ (der_107191 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_29848 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_49758 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_49949 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_49972 v h) (hints_cons _ _ _ (der_15882 v h) (hints_cons _ _ _ (der_40899 v h) (hints_cons _ _ _ (der_15876 v h) (hints_cons _ _ _ (der_44586 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_76635 v h) (hints_cons _ _ _ (der_15888 v h) (hints_cons _ _ _ (inp_12701 v h) (hints_cons _ _ _ (der_49766 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_49831 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_15670 v h) (by intro d hd; cases hd))))))))))))))))))))))))
def cl_107194 : CNF.NClause := [(75,false),(85,true),(34,false)]
theorem der_107194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107194 :=
  CNF.rup_sound cl_107194 [cl_105943,cl_79572,cl_79638,cl_15892,cl_76964,cl_15887,cl_42433,cl_15871,cl_56362,cl_15885,cl_29848,cl_15874,cl_49758,cl_15884,cl_49766,cl_15879,cl_49831,cl_15889,cl_15670,cl_79640,cl_15878,cl_12761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105943 v h) (hints_cons _ _ _ (der_79572 v h) (hints_cons _ _ _ (der_79638 v h) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_76964 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_42433 v h) (hints_cons _ _ _ (der_15871 v h) (hints_cons _ _ _ (der_56362 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_29848 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_49758 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_49766 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_49831 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_15670 v h) (hints_cons _ _ _ (der_79640 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (inp_12761 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_107195 : CNF.NClause := [(65,true),(75,false),(34,false)]
theorem der_107195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107195 :=
  CNF.rup_sound cl_107195 [cl_79884,cl_107194,cl_105766,cl_49790,cl_15868,cl_29848,cl_15874,cl_49758,cl_15884,cl_49766,cl_15879,cl_49831,cl_15889,cl_15670,cl_42525,cl_15870,cl_29841,cl_15867,cl_15693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79884 v h) (hints_cons _ _ _ (der_107194 v h) (hints_cons _ _ _ (der_105766 v h) (hints_cons _ _ _ (der_49790 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_29848 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_49758 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_49766 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_49831 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_15670 v h) (hints_cons _ _ _ (der_42525 v h) (hints_cons _ _ _ (der_15870 v h) (hints_cons _ _ _ (der_29841 v h) (hints_cons _ _ _ (der_15867 v h) (hints_cons _ _ _ (der_15693 v h) (by intro d hd; cases hd))))))))))))))))))))
def cl_107196 : CNF.NClause := [(64,false),(70,true),(48,false)]
theorem der_107196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107196 :=
  CNF.rup_sound cl_107196 [cl_79920,cl_79529,cl_49798,cl_15925,cl_76580,cl_15926,cl_76621,cl_15920,cl_54024,cl_15909,cl_76616,cl_15912,cl_76841,cl_15933,cl_13598,cl_76608,cl_15924,cl_49799,cl_15922,cl_49764,cl_15921,cl_15740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79920 v h) (hints_cons _ _ _ (der_79529 v h) (hints_cons _ _ _ (der_49798 v h) (hints_cons _ _ _ (der_15925 v h) (hints_cons _ _ _ (der_76580 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (der_76621 v h) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_54024 v h) (hints_cons _ _ _ (der_15909 v h) (hints_cons _ _ _ (der_76616 v h) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_76841 v h) (hints_cons _ _ _ (der_15933 v h) (hints_cons _ _ _ (inp_13598 v h) (hints_cons _ _ _ (der_76608 v h) (hints_cons _ _ _ (der_15924 v h) (hints_cons _ _ _ (der_49799 v h) (hints_cons _ _ _ (der_15922 v h) (hints_cons _ _ _ (der_49764 v h) (hints_cons _ _ _ (der_15921 v h) (hints_cons _ _ _ (der_15740 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_107197 : CNF.NClause := [(88,false),(83,true),(48,false)]
theorem der_107197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107197 :=
  CNF.rup_sound cl_107197 [cl_79905,cl_79529,cl_49798,cl_15925,cl_105755,cl_15911,cl_105729,cl_15931,cl_105731,cl_15910,cl_105728,cl_15929,cl_105732,cl_15917,cl_13676,cl_76608,cl_15924,cl_49799,cl_15922,cl_49764,cl_15921,cl_15740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79905 v h) (hints_cons _ _ _ (der_79529 v h) (hints_cons _ _ _ (der_49798 v h) (hints_cons _ _ _ (der_15925 v h) (hints_cons _ _ _ (der_105755 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_105729 v h) (hints_cons _ _ _ (der_15931 v h) (hints_cons _ _ _ (der_105731 v h) (hints_cons _ _ _ (der_15910 v h) (hints_cons _ _ _ (der_105728 v h) (hints_cons _ _ _ (der_15929 v h) (hints_cons _ _ _ (der_105732 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (inp_13676 v h) (hints_cons _ _ _ (der_76608 v h) (hints_cons _ _ _ (der_15924 v h) (hints_cons _ _ _ (der_49799 v h) (hints_cons _ _ _ (der_15922 v h) (hints_cons _ _ _ (der_49764 v h) (hints_cons _ _ _ (der_15921 v h) (hints_cons _ _ _ (der_15740 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_107198 : CNF.NClause := [(64,false),(76,true),(48,false)]
theorem der_107198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107198 :=
  CNF.rup_sound cl_107198 [cl_105955,cl_79529,cl_49798,cl_15925,cl_42519,cl_15932,cl_76602,cl_15916,cl_76627,cl_15907,cl_63645,cl_15930,cl_79643,cl_15914,cl_13634,cl_76608,cl_15924,cl_49764,cl_15921,cl_49799,cl_15922,cl_15740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105955 v h) (hints_cons _ _ _ (der_79529 v h) (hints_cons _ _ _ (der_49798 v h) (hints_cons _ _ _ (der_15925 v h) (hints_cons _ _ _ (der_42519 v h) (hints_cons _ _ _ (der_15932 v h) (hints_cons _ _ _ (der_76602 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_76627 v h) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_63645 v h) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_79643 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (inp_13634 v h) (hints_cons _ _ _ (der_76608 v h) (hints_cons _ _ _ (der_15924 v h) (hints_cons _ _ _ (der_49764 v h) (hints_cons _ _ _ (der_15921 v h) (hints_cons _ _ _ (der_49799 v h) (hints_cons _ _ _ (der_15922 v h) (hints_cons _ _ _ (der_15740 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_107199 : CNF.NClause := [(77,true),(83,false),(48,false)]
theorem der_107199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107199 :=
  CNF.rup_sound cl_107199 [cl_79916,cl_79529,cl_49799,cl_15882,cl_49764,cl_15881,cl_49798,cl_15885,cl_76608,cl_15884,cl_15684,cl_49763,cl_15878,cl_29811,cl_15888,cl_29842,cl_15873,cl_49782,cl_15868,cl_15669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79916 v h) (hints_cons _ _ _ (der_79529 v h) (hints_cons _ _ _ (der_49799 v h) (hints_cons _ _ _ (der_15882 v h) (hints_cons _ _ _ (der_49764 v h) (hints_cons _ _ _ (der_15881 v h) (hints_cons _ _ _ (der_49798 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_76608 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_15684 v h) (hints_cons _ _ _ (der_49763 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_29811 v h) (hints_cons _ _ _ (der_15888 v h) (hints_cons _ _ _ (der_29842 v h) (hints_cons _ _ _ (der_15873 v h) (hints_cons _ _ _ (der_49782 v h) (hints_cons _ _ _ (der_15868 v h) (hints_cons _ _ _ (der_15669 v h) (by intro d hd; cases hd)))))))))))))))))))))
def cl_107200 : CNF.NClause := [(76,false),(73,true),(41,false)]
theorem der_107200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107200 :=
  CNF.rup_sound cl_107200 [cl_80021,cl_105999,cl_78192,cl_80020,cl_79462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80021 v h) (hints_cons _ _ _ (der_105999 v h) (hints_cons _ _ _ (der_78192 v h) (hints_cons _ _ _ (der_80020 v h) (hints_cons _ _ _ (der_79462 v h) (by intro d hd; cases hd))))))
def cl_107201 : CNF.NClause := [(75,true),(73,true),(41,false)]
theorem der_107201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107201 :=
  CNF.rup_sound cl_107201 [cl_80029,cl_107200,cl_79579,cl_106004,cl_29845,cl_15879,cl_76592,cl_15874,cl_45005,cl_15889,cl_76623,cl_15884,cl_40899,cl_15869,cl_15670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80029 v h) (hints_cons _ _ _ (der_107200 v h) (hints_cons _ _ _ (der_79579 v h) (hints_cons _ _ _ (der_106004 v h) (hints_cons _ _ _ (der_29845 v h) (hints_cons _ _ _ (der_15879 v h) (hints_cons _ _ _ (der_76592 v h) (hints_cons _ _ _ (der_15874 v h) (hints_cons _ _ _ (der_45005 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_76623 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_40899 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_15670 v h) (by intro d hd; cases hd))))))))))))))))
def cl_107202 : CNF.NClause := [(75,false),(76,true),(41,false)]
theorem der_107202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107202 :=
  CNF.rup_sound cl_107202 [cl_80022,cl_79462,cl_76592,cl_13743,cl_76640,cl_14032,cl_79667,cl_14029,cl_76602,cl_14022,cl_49531,cl_14007,cl_9544,cl_76902,cl_14033,cl_79673,cl_14026,cl_76623,cl_14023,cl_76542,cl_14013,cl_76551,cl_14010,cl_9525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80022 v h) (hints_cons _ _ _ (der_79462 v h) (hints_cons _ _ _ (der_76592 v h) (hints_cons _ _ _ (inp_13743 v h) (hints_cons _ _ _ (der_76640 v h) (hints_cons _ _ _ (inp_14032 v h) (hints_cons _ _ _ (der_79667 v h) (hints_cons _ _ _ (inp_14029 v h) (hints_cons _ _ _ (der_76602 v h) (hints_cons _ _ _ (inp_14022 v h) (hints_cons _ _ _ (der_49531 v h) (hints_cons _ _ _ (inp_14007 v h) (hints_cons _ _ _ (inp_9544 v h) (hints_cons _ _ _ (der_76902 v h) (hints_cons _ _ _ (inp_14033 v h) (hints_cons _ _ _ (der_79673 v h) (hints_cons _ _ _ (inp_14026 v h) (hints_cons _ _ _ (der_76623 v h) (hints_cons _ _ _ (inp_14023 v h) (hints_cons _ _ _ (der_76542 v h) (hints_cons _ _ _ (inp_14013 v h) (hints_cons _ _ _ (der_76551 v h) (hints_cons _ _ _ (inp_14010 v h) (hints_cons _ _ _ (inp_9525 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_107203 : CNF.NClause := [(74,false),(72,true),(41,false)]
theorem der_107203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107203 :=
  CNF.rup_sound cl_107203 [cl_105996,cl_106002,cl_107200,cl_107201,cl_107202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105996 v h) (hints_cons _ _ _ (der_106002 v h) (hints_cons _ _ _ (der_107200 v h) (hints_cons _ _ _ (der_107201 v h) (hints_cons _ _ _ (der_107202 v h) (by intro d hd; cases hd))))))
def cl_107204 : CNF.NClause := [(72,true),(81,true),(43,false)]
theorem der_107204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107204 :=
  CNF.rup_sound cl_107204 [cl_105967,cl_79928,cl_79935,cl_105966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105967 v h) (hints_cons _ _ _ (der_79928 v h) (hints_cons _ _ _ (der_79935 v h) (hints_cons _ _ _ (der_105966 v h) (by intro d hd; cases hd)))))
def cl_107205 : CNF.NClause := [(91,false),(81,true),(43,false)]
theorem der_107205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107205 :=
  CNF.rup_sound cl_107205 [cl_107204,cl_105963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107204 v h) (hints_cons _ _ _ (der_105963 v h) (by intro d hd; cases hd)))
def cl_107206 : CNF.NClause := [(68,false),(72,true),(43,false)]
theorem der_107206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107206 :=
  CNF.rup_sound cl_107206 [cl_80190,cl_107204,cl_79727,cl_49763,cl_15923,cl_37368,cl_15908,cl_46318,cl_15920,cl_49818,cl_15917,cl_49832,cl_15916,cl_48585,cl_15919,cl_15739,cl_49796,cl_15913,cl_29766,cl_15928,cl_15725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80190 v h) (hints_cons _ _ _ (der_107204 v h) (hints_cons _ _ _ (der_79727 v h) (hints_cons _ _ _ (der_49763 v h) (hints_cons _ _ _ (der_15923 v h) (hints_cons _ _ _ (der_37368 v h) (hints_cons _ _ _ (der_15908 v h) (hints_cons _ _ _ (der_46318 v h) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_49818 v h) (hints_cons _ _ _ (der_15917 v h) (hints_cons _ _ _ (der_49832 v h) (hints_cons _ _ _ (der_15916 v h) (hints_cons _ _ _ (der_48585 v h) (hints_cons _ _ _ (der_15919 v h) (hints_cons _ _ _ (der_15739 v h) (hints_cons _ _ _ (der_49796 v h) (hints_cons _ _ _ (der_15913 v h) (hints_cons _ _ _ (der_29766 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (der_15725 v h) (by intro d hd; cases hd))))))))))))))))))))))
def cl_107207 : CNF.NClause := [(1059,true),(5,false),(82,true)]
theorem der_107207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107207 :=
  CNF.rup_sound cl_107207 [cl_76574,cl_15914,cl_76573,cl_15915,cl_76575,cl_15913,cl_49781,cl_15912,cl_15741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76574 v h) (hints_cons _ _ _ (der_15914 v h) (hints_cons _ _ _ (der_76573 v h) (hints_cons _ _ _ (der_15915 v h) (hints_cons _ _ _ (der_76575 v h) (hints_cons _ _ _ (der_15913 v h) (hints_cons _ _ _ (der_49781 v h) (hints_cons _ _ _ (der_15912 v h) (hints_cons _ _ _ (der_15741 v h) (by intro d hd; cases hd))))))))))
def cl_107208 : CNF.NClause := [(77,true),(143,false)]
theorem der_107208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107208 :=
  CNF.rup_sound cl_107208 [cl_15785,cl_49798,cl_59309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_49798 v h) (hints_cons _ _ _ (der_59309 v h) (by intro d hd; cases hd))))
def cl_107209 : CNF.NClause := [(57,false),(83,false),(71,true)]
theorem der_107209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107209 :=
  CNF.rup_sound cl_107209 [cl_79509,cl_76593,cl_77173,cl_29836,cl_15893,cl_29835,cl_15894,cl_29837,cl_15892,cl_15667,cl_105747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79509 v h) (hints_cons _ _ _ (der_76593 v h) (hints_cons _ _ _ (der_77173 v h) (hints_cons _ _ _ (der_29836 v h) (hints_cons _ _ _ (der_15893 v h) (hints_cons _ _ _ (der_29835 v h) (hints_cons _ _ _ (der_15894 v h) (hints_cons _ _ _ (der_29837 v h) (hints_cons _ _ _ (der_15892 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (der_105747 v h) (by intro d hd; cases hd))))))))))))
def cl_107210 : CNF.NClause := [(1055,false),(14,true),(86,true)]
theorem der_107210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107210 :=
  CNF.rup_sound cl_107210 [cl_15907,cl_43068,cl_15928,cl_15920,cl_49797,cl_15911,cl_76581,cl_15924,cl_49927,cl_15934,cl_13697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15907 v h) (hints_cons _ _ _ (der_43068 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (der_15920 v h) (hints_cons _ _ _ (der_49797 v h) (hints_cons _ _ _ (der_15911 v h) (hints_cons _ _ _ (der_76581 v h) (hints_cons _ _ _ (der_15924 v h) (hints_cons _ _ _ (der_49927 v h) (hints_cons _ _ _ (der_15934 v h) (hints_cons _ _ _ (inp_13697 v h) (by intro d hd; cases hd))))))))))))
def cl_107211 : CNF.NClause := [(903,true),(4,false),(63,true)]
theorem der_107211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107211 :=
  CNF.rup_sound cl_107211 [cl_41429,cl_15885,cl_42528,cl_15875,cl_42527,cl_15880,cl_49833,cl_15890,cl_15668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41429 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_42528 v h) (hints_cons _ _ _ (der_15875 v h) (hints_cons _ _ _ (der_42527 v h) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_49833 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_15668 v h) (by intro d hd; cases hd))))))))))
def cl_107212 : CNF.NClause := [(901,true),(2,false),(64,true)]
theorem der_107212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107212 :=
  CNF.rup_sound cl_107212 [cl_49782,cl_15883,cl_37368,cl_15878,cl_49791,cl_15873,cl_48797,cl_15888,cl_15669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49782 v h) (hints_cons _ _ _ (der_15883 v h) (hints_cons _ _ _ (der_37368 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_49791 v h) (hints_cons _ _ _ (der_15873 v h) (hints_cons _ _ _ (der_48797 v h) (hints_cons _ _ _ (der_15888 v h) (hints_cons _ _ _ (der_15669 v h) (by intro d hd; cases hd))))))))))
def cl_107214 : CNF.NClause := [(905,false),(91,true),(18,true)]
theorem der_107214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107214 :=
  CNF.rup_sound cl_107214 [cl_15872,cl_49760,cl_15891,cl_15884,cl_37342,cl_15878,cl_49793,cl_15890,cl_15715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15872 v h) (hints_cons _ _ _ (der_49760 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_37342 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_49793 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_15715 v h) (by intro d hd; cases hd))))))))))
def chunk127 : List CNF.NClause := [cl_106224,cl_106226,cl_106228,cl_106229,cl_106230,cl_106232,cl_106235,cl_106236,cl_106237,cl_106238,cl_106239,cl_106240,cl_106241,cl_106242,cl_106243,cl_106244,cl_106245,cl_106246,cl_106253,cl_106256,cl_106260,cl_106262,cl_106263,cl_106265,cl_106266,cl_106267,cl_106268,cl_106269,cl_106270,cl_106271,cl_106272,cl_106273,cl_106274,cl_106275,cl_106279,cl_106281,cl_106282,cl_106283,cl_106285,cl_106286,cl_106288,cl_106289,cl_106290,cl_106291,cl_106292,cl_106296,cl_106298,cl_106299,cl_106302,cl_106304,cl_106306,cl_106307,cl_106308,cl_106312,cl_106313,cl_106315,cl_106316,cl_106317,cl_106318,cl_106319,cl_106320,cl_106321,cl_106322,cl_106323,cl_106324,cl_106325,cl_106326,cl_106329,cl_106330,cl_106331,cl_106333,cl_106335,cl_106336,cl_106337,cl_106339,cl_106340,cl_106341,cl_106342,cl_106343,cl_106344,cl_106345,cl_106347,cl_106349,cl_106351,cl_106355,cl_106358,cl_106361,cl_106362,cl_106363,cl_106364,cl_106366,cl_106367,cl_106368,cl_106369,cl_106370,cl_106373,cl_106374,cl_106375,cl_106376,cl_106377,cl_106378,cl_106379,cl_106380,cl_106381,cl_106382,cl_106384,cl_106385,cl_106386,cl_106387,cl_106388,cl_106389,cl_106390,cl_106391,cl_106394,cl_106395,cl_106396,cl_106397,cl_106398,cl_106399,cl_106400,cl_106401,cl_106403,cl_106404,cl_106405,cl_106406,cl_106407,cl_106409,cl_106410,cl_106411,cl_106414,cl_106415,cl_106416,cl_106417,cl_106419,cl_106421,cl_106423,cl_106424,cl_106426,cl_106427,cl_106428,cl_106429,cl_106430,cl_106431,cl_106434,cl_106440,cl_106442,cl_106446,cl_106448,cl_106451,cl_106453,cl_106454,cl_106455,cl_106456,cl_106461,cl_106467,cl_106468,cl_106469,cl_106470,cl_106471,cl_106472,cl_106473,cl_106474,cl_106475,cl_106476,cl_106477,cl_106478,cl_106479,cl_106480,cl_106481,cl_106482,cl_106484,cl_106486,cl_106487,cl_106488,cl_106489,cl_106490,cl_106491,cl_106492,cl_106493,cl_106494,cl_106496,cl_106498,cl_106501,cl_106502,cl_106503,cl_106504,cl_106505,cl_106506,cl_106508,cl_106509,cl_106510,cl_106512,cl_106513,cl_106514,cl_106515,cl_106516,cl_106517,cl_106518,cl_106519,cl_106520,cl_106524,cl_106525,cl_106526,cl_106527,cl_106528,cl_106529,cl_106530,cl_106531,cl_106536,cl_106537,cl_106538,cl_106541,cl_106542,cl_106543,cl_106550,cl_106551,cl_106552,cl_106553,cl_106555,cl_106556,cl_106562,cl_106565,cl_106572,cl_106574,cl_106575,cl_106576,cl_106577,cl_106580,cl_106581,cl_106582,cl_106583,cl_106584,cl_106585,cl_106586,cl_106587,cl_106589,cl_106591,cl_106593,cl_106595,cl_106597,cl_106598,cl_106599,cl_106600,cl_106601,cl_106605,cl_106606,cl_106607,cl_106610,cl_106612,cl_106613,cl_106615,cl_106616,cl_106617,cl_106618,cl_106619,cl_106620,cl_106621,cl_106622,cl_106623,cl_106624,cl_106625,cl_106628,cl_106629,cl_106630,cl_106631,cl_106634,cl_106636,cl_106638,cl_106639,cl_106640,cl_106641,cl_106642,cl_106643,cl_106644,cl_106646,cl_106648,cl_106649,cl_106650,cl_106653,cl_106658,cl_106660,cl_106662,cl_106663,cl_106664,cl_106665,cl_106666,cl_106668,cl_106673,cl_106681,cl_106682,cl_106684,cl_106690,cl_106696,cl_106697,cl_106699,cl_106701,cl_106703,cl_106704,cl_106706,cl_106709,cl_106710,cl_106711,cl_106712,cl_106714,cl_106715,cl_106718,cl_106719,cl_106720,cl_106721,cl_106722,cl_106725,cl_106726,cl_106727,cl_106733,cl_106737,cl_106738,cl_106739,cl_106740,cl_106741,cl_106742,cl_106743,cl_106746,cl_106758,cl_106761,cl_106762,cl_106763,cl_106765,cl_106766,cl_106767,cl_106769,cl_106770,cl_106771,cl_106772,cl_106773,cl_106775,cl_106776,cl_106778,cl_106781,cl_106782,cl_106783,cl_106785,cl_106786,cl_106787,cl_106788,cl_106789,cl_106790,cl_106791,cl_106792,cl_106793,cl_106794,cl_106795,cl_106796,cl_106797,cl_106798,cl_106799,cl_106801,cl_106804,cl_106806,cl_106808,cl_106812,cl_106813,cl_106816,cl_106817,cl_106818,cl_106819,cl_106821,cl_106824,cl_106829,cl_106831,cl_106832,cl_106834,cl_106835,cl_106836,cl_106837,cl_106838,cl_106840,cl_106844,cl_106845,cl_106846,cl_106848,cl_106849,cl_106851,cl_106854,cl_106857,cl_106858,cl_106860,cl_106861,cl_106864,cl_106866,cl_106867,cl_106871,cl_106872,cl_106876,cl_106879,cl_106886,cl_106888,cl_106889,cl_106890,cl_106891,cl_106892,cl_106896,cl_106900,cl_106901,cl_106902,cl_106906,cl_106908,cl_106910,cl_106917,cl_106919,cl_106923,cl_106924,cl_106926,cl_106930,cl_106935,cl_106952,cl_106954,cl_106956,cl_106957,cl_106959,cl_106960,cl_106961,cl_106963,cl_106964,cl_106966,cl_106968,cl_106970,cl_106971,cl_106972,cl_106976,cl_106978,cl_106982,cl_106984,cl_106985,cl_106988,cl_106990,cl_106994,cl_106995,cl_107001,cl_107005,cl_107006,cl_107014,cl_107018,cl_107021,cl_107022,cl_107023,cl_107029,cl_107032,cl_107037,cl_107038,cl_107044,cl_107051,cl_107055,cl_107058,cl_107059,cl_107061,cl_107064,cl_107071,cl_107079,cl_107080,cl_107084,cl_107096,cl_107107,cl_107111,cl_107116,cl_107146,cl_107153,cl_107158,cl_107181,cl_107182,cl_107183,cl_107184,cl_107185,cl_107186,cl_107187,cl_107188,cl_107189,cl_107190,cl_107191,cl_107192,cl_107193,cl_107194,cl_107195,cl_107196,cl_107197,cl_107198,cl_107199,cl_107200,cl_107201,cl_107202,cl_107203,cl_107204,cl_107205,cl_107206,cl_107207,cl_107208,cl_107209,cl_107210,cl_107211,cl_107212,cl_107214]
theorem chunk_sound127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk127, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_106224 v h) (hints_cons _ _ _ (der_106226 v h) (hints_cons _ _ _ (der_106228 v h) (hints_cons _ _ _ (der_106229 v h) (hints_cons _ _ _ (der_106230 v h) (hints_cons _ _ _ (der_106232 v h) (hints_cons _ _ _ (der_106235 v h) (hints_cons _ _ _ (der_106236 v h) (hints_cons _ _ _ (der_106237 v h) (hints_cons _ _ _ (der_106238 v h) (hints_cons _ _ _ (der_106239 v h) (hints_cons _ _ _ (der_106240 v h) (hints_cons _ _ _ (der_106241 v h) (hints_cons _ _ _ (der_106242 v h) (hints_cons _ _ _ (der_106243 v h) (hints_cons _ _ _ (der_106244 v h) (hints_cons _ _ _ (der_106245 v h) (hints_cons _ _ _ (der_106246 v h) (hints_cons _ _ _ (der_106253 v h) (hints_cons _ _ _ (der_106256 v h) (hints_cons _ _ _ (der_106260 v h) (hints_cons _ _ _ (der_106262 v h) (hints_cons _ _ _ (der_106263 v h) (hints_cons _ _ _ (der_106265 v h) (hints_cons _ _ _ (der_106266 v h) (hints_cons _ _ _ (der_106267 v h) (hints_cons _ _ _ (der_106268 v h) (hints_cons _ _ _ (der_106269 v h) (hints_cons _ _ _ (der_106270 v h) (hints_cons _ _ _ (der_106271 v h) (hints_cons _ _ _ (der_106272 v h) (hints_cons _ _ _ (der_106273 v h) (hints_cons _ _ _ (der_106274 v h) (hints_cons _ _ _ (der_106275 v h) (hints_cons _ _ _ (der_106279 v h) (hints_cons _ _ _ (der_106281 v h) (hints_cons _ _ _ (der_106282 v h) (hints_cons _ _ _ (der_106283 v h) (hints_cons _ _ _ (der_106285 v h) (hints_cons _ _ _ (der_106286 v h) (hints_cons _ _ _ (der_106288 v h) (hints_cons _ _ _ (der_106289 v h) (hints_cons _ _ _ (der_106290 v h) (hints_cons _ _ _ (der_106291 v h) (hints_cons _ _ _ (der_106292 v h) (hints_cons _ _ _ (der_106296 v h) (hints_cons _ _ _ (der_106298 v h) (hints_cons _ _ _ (der_106299 v h) (hints_cons _ _ _ (der_106302 v h) (hints_cons _ _ _ (der_106304 v h) (hints_cons _ _ _ (der_106306 v h) (hints_cons _ _ _ (der_106307 v h) (hints_cons _ _ _ (der_106308 v h) (hints_cons _ _ _ (der_106312 v h) (hints_cons _ _ _ (der_106313 v h) (hints_cons _ _ _ (der_106315 v h) (hints_cons _ _ _ (der_106316 v h) (hints_cons _ _ _ (der_106317 v h) (hints_cons _ _ _ (der_106318 v h) (hints_cons _ _ _ (der_106319 v h) (hints_cons _ _ _ (der_106320 v h) (hints_cons _ _ _ (der_106321 v h) (hints_cons _ _ _ (der_106322 v h) (hints_cons _ _ _ (der_106323 v h) (hints_cons _ _ _ (der_106324 v h) (hints_cons _ _ _ (der_106325 v h) (hints_cons _ _ _ (der_106326 v h) (hints_cons _ _ _ (der_106329 v h) (hints_cons _ _ _ (der_106330 v h) (hints_cons _ _ _ (der_106331 v h) (hints_cons _ _ _ (der_106333 v h) (hints_cons _ _ _ (der_106335 v h) (hints_cons _ _ _ (der_106336 v h) (hints_cons _ _ _ (der_106337 v h) (hints_cons _ _ _ (der_106339 v h) (hints_cons _ _ _ (der_106340 v h) (hints_cons _ _ _ (der_106341 v h) (hints_cons _ _ _ (der_106342 v h) (hints_cons _ _ _ (der_106343 v h) (hints_cons _ _ _ (der_106344 v h) (hints_cons _ _ _ (der_106345 v h) (hints_cons _ _ _ (der_106347 v h) (hints_cons _ _ _ (der_106349 v h) (hints_cons _ _ _ (der_106351 v h) (hints_cons _ _ _ (der_106355 v h) (hints_cons _ _ _ (der_106358 v h) (hints_cons _ _ _ (der_106361 v h) (hints_cons _ _ _ (der_106362 v h) (hints_cons _ _ _ (der_106363 v h) (hints_cons _ _ _ (der_106364 v h) (hints_cons _ _ _ (der_106366 v h) (hints_cons _ _ _ (der_106367 v h) (hints_cons _ _ _ (der_106368 v h) (hints_cons _ _ _ (der_106369 v h) (hints_cons _ _ _ (der_106370 v h) (hints_cons _ _ _ (der_106373 v h) (hints_cons _ _ _ (der_106374 v h) (hints_cons _ _ _ (der_106375 v h) (hints_cons _ _ _ (der_106376 v h) (hints_cons _ _ _ (der_106377 v h) (hints_cons _ _ _ (der_106378 v h) (hints_cons _ _ _ (der_106379 v h) (hints_cons _ _ _ (der_106380 v h) (hints_cons _ _ _ (der_106381 v h) (hints_cons _ _ _ (der_106382 v h) (hints_cons _ _ _ (der_106384 v h) (hints_cons _ _ _ (der_106385 v h) (hints_cons _ _ _ (der_106386 v h) (hints_cons _ _ _ (der_106387 v h) (hints_cons _ _ _ (der_106388 v h) (hints_cons _ _ _ (der_106389 v h) (hints_cons _ _ _ (der_106390 v h) (hints_cons _ _ _ (der_106391 v h) (hints_cons _ _ _ (der_106394 v h) (hints_cons _ _ _ (der_106395 v h) (hints_cons _ _ _ (der_106396 v h) (hints_cons _ _ _ (der_106397 v h) (hints_cons _ _ _ (der_106398 v h) (hints_cons _ _ _ (der_106399 v h) (hints_cons _ _ _ (der_106400 v h) (hints_cons _ _ _ (der_106401 v h) (hints_cons _ _ _ (der_106403 v h) (hints_cons _ _ _ (der_106404 v h) (hints_cons _ _ _ (der_106405 v h) (hints_cons _ _ _ (der_106406 v h) (hints_cons _ _ _ (der_106407 v h) (hints_cons _ _ _ (der_106409 v h) (hints_cons _ _ _ (der_106410 v h) (hints_cons _ _ _ (der_106411 v h) (hints_cons _ _ _ (der_106414 v h) (hints_cons _ _ _ (der_106415 v h) (hints_cons _ _ _ (der_106416 v h) (hints_cons _ _ _ (der_106417 v h) (hints_cons _ _ _ (der_106419 v h) (hints_cons _ _ _ (der_106421 v h) (hints_cons _ _ _ (der_106423 v h) (hints_cons _ _ _ (der_106424 v h) (hints_cons _ _ _ (der_106426 v h) (hints_cons _ _ _ (der_106427 v h) (hints_cons _ _ _ (der_106428 v h) (hints_cons _ _ _ (der_106429 v h) (hints_cons _ _ _ (der_106430 v h) (hints_cons _ _ _ (der_106431 v h) (hints_cons _ _ _ (der_106434 v h) (hints_cons _ _ _ (der_106440 v h) (hints_cons _ _ _ (der_106442 v h) (hints_cons _ _ _ (der_106446 v h) (hints_cons _ _ _ (der_106448 v h) (hints_cons _ _ _ (der_106451 v h) (hints_cons _ _ _ (der_106453 v h) (hints_cons _ _ _ (der_106454 v h) (hints_cons _ _ _ (der_106455 v h) (hints_cons _ _ _ (der_106456 v h) (hints_cons _ _ _ (der_106461 v h) (hints_cons _ _ _ (der_106467 v h) (hints_cons _ _ _ (der_106468 v h) (hints_cons _ _ _ (der_106469 v h) (hints_cons _ _ _ (der_106470 v h) (hints_cons _ _ _ (der_106471 v h) (hints_cons _ _ _ (der_106472 v h) (hints_cons _ _ _ (der_106473 v h) (hints_cons _ _ _ (der_106474 v h) (hints_cons _ _ _ (der_106475 v h) (hints_cons _ _ _ (der_106476 v h) (hints_cons _ _ _ (der_106477 v h) (hints_cons _ _ _ (der_106478 v h) (hints_cons _ _ _ (der_106479 v h) (hints_cons _ _ _ (der_106480 v h) (hints_cons _ _ _ (der_106481 v h) (hints_cons _ _ _ (der_106482 v h) (hints_cons _ _ _ (der_106484 v h) (hints_cons _ _ _ (der_106486 v h) (hints_cons _ _ _ (der_106487 v h) (hints_cons _ _ _ (der_106488 v h) (hints_cons _ _ _ (der_106489 v h) (hints_cons _ _ _ (der_106490 v h) (hints_cons _ _ _ (der_106491 v h) (hints_cons _ _ _ (der_106492 v h) (hints_cons _ _ _ (der_106493 v h) (hints_cons _ _ _ (der_106494 v h) (hints_cons _ _ _ (der_106496 v h) (hints_cons _ _ _ (der_106498 v h) (hints_cons _ _ _ (der_106501 v h) (hints_cons _ _ _ (der_106502 v h) (hints_cons _ _ _ (der_106503 v h) (hints_cons _ _ _ (der_106504 v h) (hints_cons _ _ _ (der_106505 v h) (hints_cons _ _ _ (der_106506 v h) (hints_cons _ _ _ (der_106508 v h) (hints_cons _ _ _ (der_106509 v h) (hints_cons _ _ _ (der_106510 v h) (hints_cons _ _ _ (der_106512 v h) (hints_cons _ _ _ (der_106513 v h) (hints_cons _ _ _ (der_106514 v h) (hints_cons _ _ _ (der_106515 v h) (hints_cons _ _ _ (der_106516 v h) (hints_cons _ _ _ (der_106517 v h) (hints_cons _ _ _ (der_106518 v h) (hints_cons _ _ _ (der_106519 v h) (hints_cons _ _ _ (der_106520 v h) (hints_cons _ _ _ (der_106524 v h) (hints_cons _ _ _ (der_106525 v h) (hints_cons _ _ _ (der_106526 v h) (hints_cons _ _ _ (der_106527 v h) (hints_cons _ _ _ (der_106528 v h) (hints_cons _ _ _ (der_106529 v h) (hints_cons _ _ _ (der_106530 v h) (hints_cons _ _ _ (der_106531 v h) (hints_cons _ _ _ (der_106536 v h) (hints_cons _ _ _ (der_106537 v h) (hints_cons _ _ _ (der_106538 v h) (hints_cons _ _ _ (der_106541 v h) (hints_cons _ _ _ (der_106542 v h) (hints_cons _ _ _ (der_106543 v h) (hints_cons _ _ _ (der_106550 v h) (hints_cons _ _ _ (der_106551 v h) (hints_cons _ _ _ (der_106552 v h) (hints_cons _ _ _ (der_106553 v h) (hints_cons _ _ _ (der_106555 v h) (hints_cons _ _ _ (der_106556 v h) (hints_cons _ _ _ (der_106562 v h) (hints_cons _ _ _ (der_106565 v h) (hints_cons _ _ _ (der_106572 v h) (hints_cons _ _ _ (der_106574 v h) (hints_cons _ _ _ (der_106575 v h) (hints_cons _ _ _ (der_106576 v h) (hints_cons _ _ _ (der_106577 v h) (hints_cons _ _ _ (der_106580 v h) (hints_cons _ _ _ (der_106581 v h) (hints_cons _ _ _ (der_106582 v h) (hints_cons _ _ _ (der_106583 v h) (hints_cons _ _ _ (der_106584 v h) (hints_cons _ _ _ (der_106585 v h) (hints_cons _ _ _ (der_106586 v h) (hints_cons _ _ _ (der_106587 v h) (hints_cons _ _ _ (der_106589 v h) (hints_cons _ _ _ (der_106591 v h) (hints_cons _ _ _ (der_106593 v h) (hints_cons _ _ _ (der_106595 v h) (hints_cons _ _ _ (der_106597 v h) (hints_cons _ _ _ (der_106598 v h) (hints_cons _ _ _ (der_106599 v h) (hints_cons _ _ _ (der_106600 v h) (hints_cons _ _ _ (der_106601 v h) (hints_cons _ _ _ (der_106605 v h) (hints_cons _ _ _ (der_106606 v h) (hints_cons _ _ _ (der_106607 v h) (hints_cons _ _ _ (der_106610 v h) (hints_cons _ _ _ (der_106612 v h) (hints_cons _ _ _ (der_106613 v h) (hints_cons _ _ _ (der_106615 v h) (hints_cons _ _ _ (der_106616 v h) (hints_cons _ _ _ (der_106617 v h) (hints_cons _ _ _ (der_106618 v h) (hints_cons _ _ _ (der_106619 v h) (hints_cons _ _ _ (der_106620 v h) (hints_cons _ _ _ (der_106621 v h) (hints_cons _ _ _ (der_106622 v h) (hints_cons _ _ _ (der_106623 v h) (hints_cons _ _ _ (der_106624 v h) (hints_cons _ _ _ (der_106625 v h) (hints_cons _ _ _ (der_106628 v h) (hints_cons _ _ _ (der_106629 v h) (hints_cons _ _ _ (der_106630 v h) (hints_cons _ _ _ (der_106631 v h) (hints_cons _ _ _ (der_106634 v h) (hints_cons _ _ _ (der_106636 v h) (hints_cons _ _ _ (der_106638 v h) (hints_cons _ _ _ (der_106639 v h) (hints_cons _ _ _ (der_106640 v h) (hints_cons _ _ _ (der_106641 v h) (hints_cons _ _ _ (der_106642 v h) (hints_cons _ _ _ (der_106643 v h) (hints_cons _ _ _ (der_106644 v h) (hints_cons _ _ _ (der_106646 v h) (hints_cons _ _ _ (der_106648 v h) (hints_cons _ _ _ (der_106649 v h) (hints_cons _ _ _ (der_106650 v h) (hints_cons _ _ _ (der_106653 v h) (hints_cons _ _ _ (der_106658 v h) (hints_cons _ _ _ (der_106660 v h) (hints_cons _ _ _ (der_106662 v h) (hints_cons _ _ _ (der_106663 v h) (hints_cons _ _ _ (der_106664 v h) (hints_cons _ _ _ (der_106665 v h) (hints_cons _ _ _ (der_106666 v h) (hints_cons _ _ _ (der_106668 v h) (hints_cons _ _ _ (der_106673 v h) (hints_cons _ _ _ (der_106681 v h) (hints_cons _ _ _ (der_106682 v h) (hints_cons _ _ _ (der_106684 v h) (hints_cons _ _ _ (der_106690 v h) (hints_cons _ _ _ (der_106696 v h) (hints_cons _ _ _ (der_106697 v h) (hints_cons _ _ _ (der_106699 v h) (hints_cons _ _ _ (der_106701 v h) (hints_cons _ _ _ (der_106703 v h) (hints_cons _ _ _ (der_106704 v h) (hints_cons _ _ _ (der_106706 v h) (hints_cons _ _ _ (der_106709 v h) (hints_cons _ _ _ (der_106710 v h) (hints_cons _ _ _ (der_106711 v h) (hints_cons _ _ _ (der_106712 v h) (hints_cons _ _ _ (der_106714 v h) (hints_cons _ _ _ (der_106715 v h) (hints_cons _ _ _ (der_106718 v h) (hints_cons _ _ _ (der_106719 v h) (hints_cons _ _ _ (der_106720 v h) (hints_cons _ _ _ (der_106721 v h) (hints_cons _ _ _ (der_106722 v h) (hints_cons _ _ _ (der_106725 v h) (hints_cons _ _ _ (der_106726 v h) (hints_cons _ _ _ (der_106727 v h) (hints_cons _ _ _ (der_106733 v h) (hints_cons _ _ _ (der_106737 v h) (hints_cons _ _ _ (der_106738 v h) (hints_cons _ _ _ (der_106739 v h) (hints_cons _ _ _ (der_106740 v h) (hints_cons _ _ _ (der_106741 v h) (hints_cons _ _ _ (der_106742 v h) (hints_cons _ _ _ (der_106743 v h) (hints_cons _ _ _ (der_106746 v h) (hints_cons _ _ _ (der_106758 v h) (hints_cons _ _ _ (der_106761 v h) (hints_cons _ _ _ (der_106762 v h) (hints_cons _ _ _ (der_106763 v h) (hints_cons _ _ _ (der_106765 v h) (hints_cons _ _ _ (der_106766 v h) (hints_cons _ _ _ (der_106767 v h) (hints_cons _ _ _ (der_106769 v h) (hints_cons _ _ _ (der_106770 v h) (hints_cons _ _ _ (der_106771 v h) (hints_cons _ _ _ (der_106772 v h) (hints_cons _ _ _ (der_106773 v h) (hints_cons _ _ _ (der_106775 v h) (hints_cons _ _ _ (der_106776 v h) (hints_cons _ _ _ (der_106778 v h) (hints_cons _ _ _ (der_106781 v h) (hints_cons _ _ _ (der_106782 v h) (hints_cons _ _ _ (der_106783 v h) (hints_cons _ _ _ (der_106785 v h) (hints_cons _ _ _ (der_106786 v h) (hints_cons _ _ _ (der_106787 v h) (hints_cons _ _ _ (der_106788 v h) (hints_cons _ _ _ (der_106789 v h) (hints_cons _ _ _ (der_106790 v h) (hints_cons _ _ _ (der_106791 v h) (hints_cons _ _ _ (der_106792 v h) (hints_cons _ _ _ (der_106793 v h) (hints_cons _ _ _ (der_106794 v h) (hints_cons _ _ _ (der_106795 v h) (hints_cons _ _ _ (der_106796 v h) (hints_cons _ _ _ (der_106797 v h) (hints_cons _ _ _ (der_106798 v h) (hints_cons _ _ _ (der_106799 v h) (hints_cons _ _ _ (der_106801 v h) (hints_cons _ _ _ (der_106804 v h) (hints_cons _ _ _ (der_106806 v h) (hints_cons _ _ _ (der_106808 v h) (hints_cons _ _ _ (der_106812 v h) (hints_cons _ _ _ (der_106813 v h) (hints_cons _ _ _ (der_106816 v h) (hints_cons _ _ _ (der_106817 v h) (hints_cons _ _ _ (der_106818 v h) (hints_cons _ _ _ (der_106819 v h) (hints_cons _ _ _ (der_106821 v h) (hints_cons _ _ _ (der_106824 v h) (hints_cons _ _ _ (der_106829 v h) (hints_cons _ _ _ (der_106831 v h) (hints_cons _ _ _ (der_106832 v h) (hints_cons _ _ _ (der_106834 v h) (hints_cons _ _ _ (der_106835 v h) (hints_cons _ _ _ (der_106836 v h) (hints_cons _ _ _ (der_106837 v h) (hints_cons _ _ _ (der_106838 v h) (hints_cons _ _ _ (der_106840 v h) (hints_cons _ _ _ (der_106844 v h) (hints_cons _ _ _ (der_106845 v h) (hints_cons _ _ _ (der_106846 v h) (hints_cons _ _ _ (der_106848 v h) (hints_cons _ _ _ (der_106849 v h) (hints_cons _ _ _ (der_106851 v h) (hints_cons _ _ _ (der_106854 v h) (hints_cons _ _ _ (der_106857 v h) (hints_cons _ _ _ (der_106858 v h) (hints_cons _ _ _ (der_106860 v h) (hints_cons _ _ _ (der_106861 v h) (hints_cons _ _ _ (der_106864 v h) (hints_cons _ _ _ (der_106866 v h) (hints_cons _ _ _ (der_106867 v h) (hints_cons _ _ _ (der_106871 v h) (hints_cons _ _ _ (der_106872 v h) (hints_cons _ _ _ (der_106876 v h) (hints_cons _ _ _ (der_106879 v h) (hints_cons _ _ _ (der_106886 v h) (hints_cons _ _ _ (der_106888 v h) (hints_cons _ _ _ (der_106889 v h) (hints_cons _ _ _ (der_106890 v h) (hints_cons _ _ _ (der_106891 v h) (hints_cons _ _ _ (der_106892 v h) (hints_cons _ _ _ (der_106896 v h) (hints_cons _ _ _ (der_106900 v h) (hints_cons _ _ _ (der_106901 v h) (hints_cons _ _ _ (der_106902 v h) (hints_cons _ _ _ (der_106906 v h) (hints_cons _ _ _ (der_106908 v h) (hints_cons _ _ _ (der_106910 v h) (hints_cons _ _ _ (der_106917 v h) (hints_cons _ _ _ (der_106919 v h) (hints_cons _ _ _ (der_106923 v h) (hints_cons _ _ _ (der_106924 v h) (hints_cons _ _ _ (der_106926 v h) (hints_cons _ _ _ (der_106930 v h) (hints_cons _ _ _ (der_106935 v h) (hints_cons _ _ _ (der_106952 v h) (hints_cons _ _ _ (der_106954 v h) (hints_cons _ _ _ (der_106956 v h) (hints_cons _ _ _ (der_106957 v h) (hints_cons _ _ _ (der_106959 v h) (hints_cons _ _ _ (der_106960 v h) (hints_cons _ _ _ (der_106961 v h) (hints_cons _ _ _ (der_106963 v h) (hints_cons _ _ _ (der_106964 v h) (hints_cons _ _ _ (der_106966 v h) (hints_cons _ _ _ (der_106968 v h) (hints_cons _ _ _ (der_106970 v h) (hints_cons _ _ _ (der_106971 v h) (hints_cons _ _ _ (der_106972 v h) (hints_cons _ _ _ (der_106976 v h) (hints_cons _ _ _ (der_106978 v h) (hints_cons _ _ _ (der_106982 v h) (hints_cons _ _ _ (der_106984 v h) (hints_cons _ _ _ (der_106985 v h) (hints_cons _ _ _ (der_106988 v h) (hints_cons _ _ _ (der_106990 v h) (hints_cons _ _ _ (der_106994 v h) (hints_cons _ _ _ (der_106995 v h) (hints_cons _ _ _ (der_107001 v h) (hints_cons _ _ _ (der_107005 v h) (hints_cons _ _ _ (der_107006 v h) (hints_cons _ _ _ (der_107014 v h) (hints_cons _ _ _ (der_107018 v h) (hints_cons _ _ _ (der_107021 v h) (hints_cons _ _ _ (der_107022 v h) (hints_cons _ _ _ (der_107023 v h) (hints_cons _ _ _ (der_107029 v h) (hints_cons _ _ _ (der_107032 v h) (hints_cons _ _ _ (der_107037 v h) (hints_cons _ _ _ (der_107038 v h) (hints_cons _ _ _ (der_107044 v h) (hints_cons _ _ _ (der_107051 v h) (hints_cons _ _ _ (der_107055 v h) (hints_cons _ _ _ (der_107058 v h) (hints_cons _ _ _ (der_107059 v h) (hints_cons _ _ _ (der_107061 v h) (hints_cons _ _ _ (der_107064 v h) (hints_cons _ _ _ (der_107071 v h) (hints_cons _ _ _ (der_107079 v h) (hints_cons _ _ _ (der_107080 v h) (hints_cons _ _ _ (der_107084 v h) (hints_cons _ _ _ (der_107096 v h) (hints_cons _ _ _ (der_107107 v h) (hints_cons _ _ _ (der_107111 v h) (hints_cons _ _ _ (der_107116 v h) (hints_cons _ _ _ (der_107146 v h) (hints_cons _ _ _ (der_107153 v h) (hints_cons _ _ _ (der_107158 v h) (hints_cons _ _ _ (der_107181 v h) (hints_cons _ _ _ (der_107182 v h) (hints_cons _ _ _ (der_107183 v h) (hints_cons _ _ _ (der_107184 v h) (hints_cons _ _ _ (der_107185 v h) (hints_cons _ _ _ (der_107186 v h) (hints_cons _ _ _ (der_107187 v h) (hints_cons _ _ _ (der_107188 v h) (hints_cons _ _ _ (der_107189 v h) (hints_cons _ _ _ (der_107190 v h) (hints_cons _ _ _ (der_107191 v h) (hints_cons _ _ _ (der_107192 v h) (hints_cons _ _ _ (der_107193 v h) (hints_cons _ _ _ (der_107194 v h) (hints_cons _ _ _ (der_107195 v h) (hints_cons _ _ _ (der_107196 v h) (hints_cons _ _ _ (der_107197 v h) (hints_cons _ _ _ (der_107198 v h) (hints_cons _ _ _ (der_107199 v h) (hints_cons _ _ _ (der_107200 v h) (hints_cons _ _ _ (der_107201 v h) (hints_cons _ _ _ (der_107202 v h) (hints_cons _ _ _ (der_107203 v h) (hints_cons _ _ _ (der_107204 v h) (hints_cons _ _ _ (der_107205 v h) (hints_cons _ _ _ (der_107206 v h) (hints_cons _ _ _ (der_107207 v h) (hints_cons _ _ _ (der_107208 v h) (hints_cons _ _ _ (der_107209 v h) (hints_cons _ _ _ (der_107210 v h) (hints_cons _ _ _ (der_107211 v h) (hints_cons _ _ _ (der_107212 v h) (hints_cons _ _ _ (der_107214 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix127 := prefix126 ++ chunk127
theorem prefix_sound127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix127, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound126 v h c hc
  · exact chunk_sound127 v h c hc
end Percolation.NReplay
