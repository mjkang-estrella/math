import NReplay182
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_138320 : CNF.NClause := [(60,false),(144,false),(50,false),(152,false),(46,false),(52,false),(53,false)]
theorem der_138320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138320 :=
  CNF.rup_sound cl_138320 [cl_136298,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136298 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_138321 : CNF.NClause := [(34,false),(60,false),(126,false),(125,false),(143,false),(52,false),(152,false)]
theorem der_138321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138321 :=
  CNF.rup_sound cl_138321 [cl_136617,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136617 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_138322 : CNF.NClause := [(141,false),(48,true),(70,false),(83,false),(88,false),(21,false),(64,false)]
theorem der_138322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138322 :=
  CNF.rup_sound cl_138322 [cl_136714,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136714 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_138323 : CNF.NClause := [(97,false),(152,false),(98,false),(119,false),(52,false),(143,false),(110,false)]
theorem der_138323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138323 :=
  CNF.rup_sound cl_138323 [cl_136834,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136834 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_138324 : CNF.NClause := [(29,false),(52,true),(85,false),(66,false),(73,false),(21,false),(79,false),(67,false)]
theorem der_138324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138324 :=
  CNF.rup_sound cl_138324 [cl_41794,cl_109923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_41794 v h) (hints_cons _ _ _ (der_109923 v h) (by intro d hd; cases hd)))
def cl_138325 : CNF.NClause := [(52,true),(17,false),(66,false),(79,false),(73,false),(21,false),(67,false),(85,false)]
theorem der_138325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138325 :=
  CNF.rup_sound cl_138325 [cl_43966,cl_109923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_43966 v h) (hints_cons _ _ _ (der_109923 v h) (by intro d hd; cases hd)))
def cl_138327 : CNF.NClause := [(101,false),(104,false),(86,false),(112,false),(153,false),(59,false),(137,false),(121,false)]
theorem der_138327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138327 :=
  CNF.rup_sound cl_138327 [cl_107504,cl_88594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107504 v h) (hints_cons _ _ _ (der_88594 v h) (by intro d hd; cases hd)))
def cl_138328 : CNF.NClause := [(23,false),(27,false),(81,false),(74,false),(17,false),(67,false),(54,true),(65,false)]
theorem der_138328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138328 :=
  CNF.rup_sound cl_138328 [cl_66788,cl_124722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66788 v h) (hints_cons _ _ _ (der_124722 v h) (by intro d hd; cases hd)))
def cl_138331 : CNF.NClause := [(132,true),(140,true),(151,true),(152,true),(55,true),(148,false),(128,false),(144,true)]
theorem der_138331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138331 :=
  CNF.rup_sound cl_138331 [cl_107510,cl_110763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107510 v h) (hints_cons _ _ _ (der_110763 v h) (by intro d hd; cases hd)))
def cl_138332 : CNF.NClause := [(38,false),(146,false),(111,false),(152,false),(84,false),(113,false),(120,false),(102,false)]
theorem der_138332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138332 :=
  CNF.rup_sound cl_138332 [cl_107512,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107512 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_138333 : CNF.NClause := [(99,false),(146,false),(97,false),(84,false),(120,false),(108,false),(47,false),(152,false)]
theorem der_138333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138333 :=
  CNF.rup_sound cl_138333 [cl_107513,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107513 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_138334 : CNF.NClause := [(146,false),(94,false),(84,false),(152,false),(107,false),(55,false),(111,false),(122,false)]
theorem der_138334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138334 :=
  CNF.rup_sound cl_138334 [cl_107514,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107514 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_138335 : CNF.NClause := [(38,false),(111,false),(104,false),(129,false),(71,false),(144,false),(95,false),(120,false)]
theorem der_138335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138335 :=
  CNF.rup_sound cl_138335 [cl_107515,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107515 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138336 : CNF.NClause := [(123,false),(152,false),(116,false),(36,false),(117,false),(132,false),(128,false),(114,false)]
theorem der_138336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138336 :=
  CNF.rup_sound cl_138336 [cl_107520,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107520 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_138337 : CNF.NClause := [(109,false),(58,false),(100,false),(125,false),(75,false),(127,false),(93,false),(120,false)]
theorem der_138337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138337 :=
  CNF.rup_sound cl_138337 [cl_107521,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107521 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138338 : CNF.NClause := [(109,false),(126,false),(120,false),(58,false),(107,false),(131,true),(93,false),(127,false)]
theorem der_138338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138338 :=
  CNF.rup_sound cl_138338 [cl_107522,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107522 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138339 : CNF.NClause := [(127,false),(99,false),(108,false),(47,false),(85,false),(115,false),(125,false),(120,false)]
theorem der_138339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138339 :=
  CNF.rup_sound cl_138339 [cl_107523,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107523 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_138340 : CNF.NClause := [(50,false),(132,false),(126,false),(84,false),(135,false),(37,false),(128,false),(104,false)]
theorem der_138340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138340 :=
  CNF.rup_sound cl_138340 [cl_107525,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107525 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_138341 : CNF.NClause := [(118,false),(109,false),(129,false),(144,false),(71,false),(94,false),(35,false),(104,false)]
theorem der_138341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138341 :=
  CNF.rup_sound cl_138341 [cl_107526,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107526 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138343 : CNF.NClause := [(104,false),(128,false),(119,false),(98,false),(130,false),(150,false),(116,false),(52,false)]
theorem der_138343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138343 :=
  CNF.rup_sound cl_138343 [cl_107528,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107528 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_138344 : CNF.NClause := [(45,false),(117,false),(128,false),(126,false),(103,false),(120,false),(135,false),(101,false)]
theorem der_138344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138344 :=
  CNF.rup_sound cl_138344 [cl_107529,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107529 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138346 : CNF.NClause := [(95,false),(118,false),(152,false),(105,false),(135,false),(83,false),(110,false),(33,false)]
theorem der_138346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138346 :=
  CNF.rup_sound cl_138346 [cl_107531,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107531 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_138347 : CNF.NClause := [(38,false),(45,false),(144,false),(139,false),(37,false),(112,false),(49,false),(78,false)]
theorem der_138347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138347 :=
  CNF.rup_sound cl_138347 [cl_107532,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107532 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_138348 : CNF.NClause := [(111,false),(126,false),(64,false),(60,false),(93,false),(117,false),(128,false),(119,false)]
theorem der_138348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138348 :=
  CNF.rup_sound cl_138348 [cl_107536,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107536 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138349 : CNF.NClause := [(43,false),(126,false),(71,false),(129,false),(32,false),(128,false),(37,false),(144,false)]
theorem der_138349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138349 :=
  CNF.rup_sound cl_138349 [cl_107537,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107537 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138350 : CNF.NClause := [(100,false),(2,false),(128,false),(33,false),(136,false),(110,false),(105,false),(148,false)]
theorem der_138350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138350 :=
  CNF.rup_sound cl_138350 [cl_107538,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107538 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_138351 : CNF.NClause := [(93,false),(59,false),(121,false),(139,false),(129,false),(101,false),(104,false),(84,false)]
theorem der_138351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138351 :=
  CNF.rup_sound cl_138351 [cl_109198,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109198 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138352 : CNF.NClause := [(93,false),(146,false),(152,false),(84,false),(104,false),(37,false),(43,false),(55,false)]
theorem der_138352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138352 :=
  CNF.rup_sound cl_138352 [cl_107540,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107540 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_138353 : CNF.NClause := [(101,false),(126,false),(97,false),(37,false),(113,false),(135,false),(122,false),(128,false)]
theorem der_138353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138353 :=
  CNF.rup_sound cl_138353 [cl_107542,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107542 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138355 : CNF.NClause := [(89,false),(117,true),(53,false),(88,false),(142,true),(129,true),(146,false),(125,true)]
theorem der_138355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138355 :=
  CNF.rup_sound cl_138355 [cl_90358,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90358 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_138356 : CNF.NClause := [(38,false),(102,false),(128,false),(148,false),(120,false),(104,false),(95,false),(130,false)]
theorem der_138356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138356 :=
  CNF.rup_sound cl_138356 [cl_107549,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107549 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138357 : CNF.NClause := [(45,false),(38,false),(128,false),(135,false),(152,false),(126,false),(50,false),(63,false)]
theorem der_138357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138357 :=
  CNF.rup_sound cl_138357 [cl_107550,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107550 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_138358 : CNF.NClause := [(113,false),(38,false),(120,false),(102,false),(84,false),(128,false),(111,false),(126,false)]
theorem der_138358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138358 :=
  CNF.rup_sound cl_138358 [cl_107551,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107551 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_138359 : CNF.NClause := [(138,false),(143,true),(49,true),(142,false),(129,true),(132,true),(131,true),(128,true)]
theorem der_138359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138359 :=
  CNF.rup_sound cl_138359 [cl_107553,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107553 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_138360 : CNF.NClause := [(49,true),(145,true),(140,true),(125,true),(138,false),(142,false),(134,true),(137,true)]
theorem der_138360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138360 :=
  CNF.rup_sound cl_138360 [cl_107554,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107554 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_138361 : CNF.NClause := [(101,false),(51,false),(99,false),(137,false),(67,false),(145,false),(100,false),(123,false)]
theorem der_138361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138361 :=
  CNF.rup_sound cl_138361 [cl_107555,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107555 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_138362 : CNF.NClause := [(101,false),(37,false),(122,false),(134,false),(113,false),(97,false),(75,false),(139,false)]
theorem der_138362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138362 :=
  CNF.rup_sound cl_138362 [cl_107556,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107556 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_138363 : CNF.NClause := [(95,false),(103,false),(133,false),(43,false),(122,false),(63,false),(116,false),(153,false)]
theorem der_138363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138363 :=
  CNF.rup_sound cl_138363 [cl_107559,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107559 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_138364 : CNF.NClause := [(120,false),(129,false),(139,false),(103,false),(45,false),(94,false),(138,false),(101,false)]
theorem der_138364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138364 :=
  CNF.rup_sound cl_138364 [cl_107560,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107560 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138365 : CNF.NClause := [(151,false),(138,false),(102,false),(98,false),(99,false),(51,false),(85,false),(123,false)]
theorem der_138365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138365 :=
  CNF.rup_sound cl_138365 [cl_107561,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107561 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_138366 : CNF.NClause := [(66,true),(1075,false),(1070,true),(73,false),(67,false),(88,false),(52,true),(79,false)]
theorem der_138366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138366 :=
  CNF.rup_sound cl_138366 [cl_100945,cl_132315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100945 v h) (hints_cons _ _ _ (der_132315 v h) (by intro d hd; cases hd)))
def cl_138367 : CNF.NClause := [(39,false),(136,false),(59,false),(44,false),(60,false),(130,false),(42,false),(64,false)]
theorem der_138367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138367 :=
  CNF.rup_sound cl_138367 [cl_107567,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107567 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_138368 : CNF.NClause := [(93,false),(111,false),(126,false),(119,false),(60,false),(99,false),(131,true),(125,false)]
theorem der_138368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138368 :=
  CNF.rup_sound cl_138368 [cl_107568,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107568 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138369 : CNF.NClause := [(34,false),(111,false),(116,false),(133,false),(96,false),(77,false),(141,false),(118,false)]
theorem der_138369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138369 :=
  CNF.rup_sound cl_138369 [cl_104684,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104684 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_138370 : CNF.NClause := [(131,false),(138,false),(84,false),(142,true),(143,true),(136,true),(141,true),(85,false)]
theorem der_138370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138370 :=
  CNF.rup_sound cl_138370 [cl_109866,cl_56745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109866 v h) (hints_cons _ _ _ (der_56745 v h) (by intro d hd; cases hd)))
def cl_138371 : CNF.NClause := [(131,false),(138,false),(143,true),(141,true),(85,false),(146,true),(142,true),(136,true)]
theorem der_138371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138371 :=
  CNF.rup_sound cl_138371 [cl_109851,cl_56745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109851 v h) (hints_cons _ _ _ (der_56745 v h) (by intro d hd; cases hd)))
def cl_138374 : CNF.NClause := [(45,false),(58,false),(99,false),(153,false),(141,false),(34,false),(70,false),(37,false)]
theorem der_138374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138374 :=
  CNF.rup_sound cl_138374 [cl_109306,cl_15794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109306 v h) (hints_cons _ _ _ (der_15794 v h) (by intro d hd; cases hd)))
def cl_138375 : CNF.NClause := [(101,false),(48,false),(140,false),(107,false),(114,false),(131,false),(68,false),(119,false)]
theorem der_138375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138375 :=
  CNF.rup_sound cl_138375 [cl_108644,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108644 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138376 : CNF.NClause := [(99,false),(134,false),(139,false),(118,false),(114,false),(128,false),(94,false),(35,false)]
theorem der_138376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138376 :=
  CNF.rup_sound cl_138376 [cl_107574,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138377 : CNF.NClause := [(34,false),(101,false),(133,false),(52,false),(118,false),(96,false),(111,false),(63,false)]
theorem der_138377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138377 :=
  CNF.rup_sound cl_138377 [cl_109833,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109833 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138378 : CNF.NClause := [(133,false),(118,false),(96,false),(34,false),(128,false),(145,false),(111,false),(101,false)]
theorem der_138378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138378 :=
  CNF.rup_sound cl_138378 [cl_109832,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109832 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138379 : CNF.NClause := [(141,false),(105,false),(146,false),(50,false),(94,false),(116,false),(137,false),(77,false)]
theorem der_138379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138379 :=
  CNF.rup_sound cl_138379 [cl_106424,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106424 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138380 : CNF.NClause := [(52,true),(9,false),(85,false),(73,false),(21,false),(6,false),(147,false),(79,false)]
theorem der_138380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138380 :=
  CNF.rup_sound cl_138380 [cl_109834,cl_43827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109834 v h) (hints_cons _ _ _ (der_43827 v h) (by intro d hd; cases hd)))
def cl_138381 : CNF.NClause := [(102,false),(116,false),(121,false),(50,false),(68,false),(94,false),(147,false),(140,false)]
theorem der_138381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138381 :=
  CNF.rup_sound cl_138381 [cl_108809,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108809 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138383 : CNF.NClause := [(117,false),(110,false),(120,false),(45,false),(133,false),(137,false),(101,false),(82,false)]
theorem der_138383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138383 :=
  CNF.rup_sound cl_138383 [cl_107570,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107570 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_138385 : CNF.NClause := [(117,false),(132,false),(123,false),(116,false),(69,false),(115,false),(135,false),(36,false)]
theorem der_138385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138385 :=
  CNF.rup_sound cl_138385 [cl_107569,cl_86552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107569 v h) (hints_cons _ _ _ (der_86552 v h) (by intro d hd; cases hd)))
def cl_138387 : CNF.NClause := [(116,false),(101,false),(96,false),(131,false),(34,false),(118,false),(140,false),(68,false)]
theorem der_138387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138387 :=
  CNF.rup_sound cl_138387 [cl_108649,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108649 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138389 : CNF.NClause := [(47,false),(114,false),(137,false),(101,false),(141,false),(95,false),(70,false),(39,false)]
theorem der_138389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138389 :=
  CNF.rup_sound cl_138389 [cl_108393,cl_15779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108393 v h) (hints_cons _ _ _ (der_15779 v h) (by intro d hd; cases hd)))
def cl_138392 : CNF.NClause := [(138,false),(131,false),(118,false),(99,false),(129,false),(139,false),(35,false),(78,false)]
theorem der_138392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138392 :=
  CNF.rup_sound cl_138392 [cl_110526,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110526 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138394 : CNF.NClause := [(109,false),(129,false),(134,false),(102,false),(96,false),(119,false),(86,false),(44,false)]
theorem der_138394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138394 :=
  CNF.rup_sound cl_138394 [cl_116250,cl_137961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116250 v h) (hints_cons _ _ _ (der_137961 v h) (by intro d hd; cases hd)))
def cl_138395 : CNF.NClause := [(54,false),(113,false),(53,false),(50,false),(49,false),(137,false),(69,false),(133,false)]
theorem der_138395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138395 :=
  CNF.rup_sound cl_138395 [cl_116068,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116068 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_138396 : CNF.NClause := [(96,false),(54,false),(145,false),(133,false),(120,false),(114,false),(63,false),(105,false)]
theorem der_138396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138396 :=
  CNF.rup_sound cl_138396 [cl_113203,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113203 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138397 : CNF.NClause := [(45,false),(54,false),(133,false),(141,false),(39,false),(140,false),(77,false),(131,false)]
theorem der_138397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138397 :=
  CNF.rup_sound cl_138397 [cl_113369,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113369 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138398 : CNF.NClause := [(54,false),(118,false),(95,false),(33,false),(138,false),(129,false),(81,false),(144,false)]
theorem der_138398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138398 :=
  CNF.rup_sound cl_138398 [cl_113103,cl_107248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113103 v h) (hints_cons _ _ _ (der_107248 v h) (by intro d hd; cases hd)))
def cl_138399 : CNF.NClause := [(39,false),(125,false),(113,false),(127,false),(110,false),(138,false),(99,false),(135,false)]
theorem der_138399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138399 :=
  CNF.rup_sound cl_138399 [cl_113702,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113702 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_138400 : CNF.NClause := [(96,false),(54,false),(105,false),(141,false),(145,false),(112,false),(120,false),(139,true)]
theorem der_138400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138400 :=
  CNF.rup_sound cl_138400 [cl_113067,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113067 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_138401 : CNF.NClause := [(57,false),(38,false),(107,false),(59,false),(49,false),(145,false),(141,false),(139,true)]
theorem der_138401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138401 :=
  CNF.rup_sound cl_138401 [cl_114220,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114220 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_138402 : CNF.NClause := [(57,false),(126,false),(64,false),(59,false),(39,false),(53,false),(128,false),(50,false)]
theorem der_138402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138402 :=
  CNF.rup_sound cl_138402 [cl_116856,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116856 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138403 : CNF.NClause := [(913,false),(89,false),(79,false),(86,false),(912,true),(63,false),(45,true),(70,false)]
theorem der_138403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138403 :=
  CNF.rup_sound cl_138403 [cl_116138,cl_107285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116138 v h) (hints_cons _ _ _ (der_107285 v h) (by intro d hd; cases hd)))
def cl_138404 : CNF.NClause := [(151,false),(50,false),(125,true),(116,true),(18,false),(152,false),(133,true),(139,true)]
theorem der_138404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138404 :=
  CNF.rup_sound cl_138404 [cl_116384,cl_75861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116384 v h) (hints_cons _ _ _ (der_75861 v h) (by intro d hd; cases hd)))
def cl_138405 : CNF.NClause := [(47,false),(97,false),(108,false),(120,false),(133,false),(99,false),(63,false),(137,false)]
theorem der_138405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138405 :=
  CNF.rup_sound cl_138405 [cl_111989,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111989 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_138407 : CNF.NClause := [(101,false),(110,false),(94,false),(103,false),(140,false),(138,false),(117,false),(75,false)]
theorem der_138407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138407 :=
  CNF.rup_sound cl_138407 [cl_111960,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111960 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_138410 : CNF.NClause := [(13,false),(84,true),(71,true),(1,true),(24,true),(5,true),(20,true),(26,true)]
theorem der_138410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138410 :=
  CNF.rup_sound cl_138410 [cl_113318,cl_49777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113318 v h) (hints_cons _ _ _ (der_49777 v h) (by intro d hd; cases hd)))
def cl_138411 : CNF.NClause := [(111,false),(142,false),(99,false),(60,false),(150,false),(119,false),(62,false),(105,false)]
theorem der_138411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138411 :=
  CNF.rup_sound cl_138411 [cl_110889,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110889 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_138412 : CNF.NClause := [(96,false),(34,false),(128,false),(153,false),(116,false),(133,false),(101,false),(80,false)]
theorem der_138412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138412 :=
  CNF.rup_sound cl_138412 [cl_110452,cl_67558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110452 v h) (hints_cons _ _ _ (der_67558 v h) (by intro d hd; cases hd)))
def cl_138414 : CNF.NClause := [(103,false),(100,false),(42,false),(121,false),(130,false),(150,false),(111,false),(79,false)]
theorem der_138414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138414 :=
  CNF.rup_sound cl_138414 [cl_110938,cl_88593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110938 v h) (hints_cons _ _ _ (der_88593 v h) (by intro d hd; cases hd)))
def cl_138416 : CNF.NClause := [(100,false),(140,false),(112,false),(113,false),(40,false),(138,false),(68,false),(119,false)]
theorem der_138416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138416 :=
  CNF.rup_sound cl_138416 [cl_111318,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111318 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138417 : CNF.NClause := [(133,false),(109,false),(145,false),(121,false),(117,false),(63,false),(95,false),(53,false)]
theorem der_138417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138417 :=
  CNF.rup_sound cl_138417 [cl_113991,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113991 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138418 : CNF.NClause := [(109,false),(140,false),(68,false),(138,false),(102,false),(96,false),(44,false),(119,false)]
theorem der_138418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138418 :=
  CNF.rup_sound cl_138418 [cl_112091,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112091 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138419 : CNF.NClause := [(44,false),(150,false),(48,false),(130,false),(151,true),(152,true),(133,false),(39,false)]
theorem der_138419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138419 :=
  CNF.rup_sound cl_138419 [cl_120534,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120534 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_138420 : CNF.NClause := [(126,false),(39,false),(64,false),(60,false),(128,false),(48,false),(40,false),(59,false)]
theorem der_138420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138420 :=
  CNF.rup_sound cl_138420 [cl_122409,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122409 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138422 : CNF.NClause := [(97,false),(51,false),(39,false),(111,false),(134,false),(114,false),(42,false),(143,false)]
theorem der_138422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138422 :=
  CNF.rup_sound cl_138422 [cl_117491,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117491 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138424 : CNF.NClause := [(38,false),(113,false),(120,false),(104,false),(148,false),(95,false),(150,false),(79,false)]
theorem der_138424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138424 :=
  CNF.rup_sound cl_138424 [cl_122023,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122023 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138425 : CNF.NClause := [(112,false),(104,false),(121,false),(129,false),(144,false),(59,false),(93,false),(70,false)]
theorem der_138425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138425 :=
  CNF.rup_sound cl_138425 [cl_121316,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121316 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138427 : CNF.NClause := [(919,false),(10,false),(913,true),(69,false),(68,false),(51,true),(905,true),(916,true)]
theorem der_138427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138427 :=
  CNF.rup_sound cl_138427 [cl_120863,cl_124822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120863 v h) (hints_cons _ _ _ (der_124822 v h) (by intro d hd; cases hd)))
def cl_138429 : CNF.NClause := [(117,false),(106,false),(121,false),(141,false),(109,false),(77,false),(145,false),(53,false)]
theorem der_138429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138429 :=
  CNF.rup_sound cl_138429 [cl_121090,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121090 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_138430 : CNF.NClause := [(94,true),(143,true),(13,false),(67,false),(138,true),(12,false),(128,true),(148,false)]
theorem der_138430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138430 :=
  CNF.rup_sound cl_138430 [cl_120167,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120167 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138431 : CNF.NClause := [(99,false),(137,false),(150,false),(136,false),(50,false),(141,false),(112,false),(68,false)]
theorem der_138431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138431 :=
  CNF.rup_sound cl_138431 [cl_118832,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118832 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_138432 : CNF.NClause := [(50,false),(150,false),(141,false),(153,false),(142,false),(106,false),(71,false),(39,false)]
theorem der_138432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138432 :=
  CNF.rup_sound cl_138432 [cl_119851,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119851 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138435 : CNF.NClause := [(52,false),(141,false),(77,false),(94,false),(121,false),(105,false),(50,false),(102,false)]
theorem der_138435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138435 :=
  CNF.rup_sound cl_138435 [cl_119180,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119180 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138436 : CNF.NClause := [(47,false),(108,false),(97,false),(99,false),(127,false),(126,false),(84,false),(120,false)]
theorem der_138436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138436 :=
  CNF.rup_sound cl_138436 [cl_121003,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121003 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_138437 : CNF.NClause := [(58,false),(114,false),(136,false),(152,true),(150,false),(47,false),(143,false),(39,false)]
theorem der_138437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138437 :=
  CNF.rup_sound cl_138437 [cl_117495,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117495 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_138439 : CNF.NClause := [(923,false),(55,true),(928,true),(63,false),(906,true),(76,false),(84,false),(91,false)]
theorem der_138439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138439 :=
  CNF.rup_sound cl_138439 [cl_119673,cl_62077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119673 v h) (hints_cons _ _ _ (der_62077 v h) (by intro d hd; cases hd)))
def cl_138440 : CNF.NClause := [(50,false),(126,false),(48,false),(60,false),(127,false),(64,false),(106,false),(39,false)]
theorem der_138440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138440 :=
  CNF.rup_sound cl_138440 [cl_119794,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119794 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138441 : CNF.NClause := [(39,false),(143,false),(49,false),(137,false),(91,false),(24,false),(135,false),(145,false)]
theorem der_138441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138441 :=
  CNF.rup_sound cl_138441 [cl_118370,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118370 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_138442 : CNF.NClause := [(59,false),(135,false),(130,false),(53,false),(50,false),(150,false),(71,false),(39,false)]
theorem der_138442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138442 :=
  CNF.rup_sound cl_138442 [cl_119691,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119691 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138444 : CNF.NClause := [(102,false),(141,false),(145,false),(105,false),(50,false),(94,false),(121,false),(77,false)]
theorem der_138444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138444 :=
  CNF.rup_sound cl_138444 [cl_119179,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119179 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138445 : CNF.NClause := [(121,false),(105,false),(108,false),(136,false),(102,false),(148,false),(50,false),(63,false)]
theorem der_138445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138445 :=
  CNF.rup_sound cl_138445 [cl_119146,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119146 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138446 : CNF.NClause := [(140,false),(151,false),(105,false),(68,false),(94,false),(50,false),(121,false),(102,false)]
theorem der_138446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138446 :=
  CNF.rup_sound cl_138446 [cl_119352,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119352 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138447 : CNF.NClause := [(99,false),(108,false),(120,false),(97,false),(82,false),(129,false),(47,false),(134,false)]
theorem der_138447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138447 :=
  CNF.rup_sound cl_138447 [cl_117503,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117503 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138448 : CNF.NClause := [(121,false),(105,false),(145,false),(67,false),(137,false),(94,false),(108,false),(50,false)]
theorem der_138448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138448 :=
  CNF.rup_sound cl_138448 [cl_128029,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128029 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_138451 : CNF.NClause := [(36,false),(133,false),(150,false),(142,false),(83,false),(43,false),(137,false),(50,false)]
theorem der_138451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138451 :=
  CNF.rup_sound cl_138451 [cl_126820,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126820 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138452 : CNF.NClause := [(57,false),(114,false),(144,false),(134,false),(122,false),(110,false),(75,false),(93,false)]
theorem der_138452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138452 :=
  CNF.rup_sound cl_138452 [cl_124413,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124413 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_138453 : CNF.NClause := [(134,false),(108,false),(115,false),(144,false),(120,false),(47,false),(97,false),(75,false)]
theorem der_138453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138453 :=
  CNF.rup_sound cl_138453 [cl_130102,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130102 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_138454 : CNF.NClause := [(45,false),(59,false),(150,false),(108,false),(142,false),(83,false),(44,false),(42,false)]
theorem der_138454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138454 :=
  CNF.rup_sound cl_138454 [cl_127072,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127072 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_138455 : CNF.NClause := [(109,false),(142,false),(150,false),(44,false),(115,false),(119,false),(103,false),(83,false)]
theorem der_138455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138455 :=
  CNF.rup_sound cl_138455 [cl_128454,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128454 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138456 : CNF.NClause := [(34,false),(142,false),(126,false),(50,false),(150,false),(121,false),(83,false),(94,false)]
theorem der_138456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138456 :=
  CNF.rup_sound cl_138456 [cl_129681,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129681 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138457 : CNF.NClause := [(121,false),(129,false),(96,false),(83,false),(39,false),(99,false),(110,false),(134,false)]
theorem der_138457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138457 :=
  CNF.rup_sound cl_138457 [cl_125391,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125391 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_138458 : CNF.NClause := [(4,false),(24,false),(148,true),(76,false),(80,false),(67,false),(55,true),(84,false)]
theorem der_138458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138458 :=
  CNF.rup_sound cl_138458 [cl_127185,cl_49833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127185 v h) (hints_cons _ _ _ (der_49833 v h) (by intro d hd; cases hd)))
def cl_138460 : CNF.NClause := [(142,false),(103,false),(97,false),(114,false),(148,false),(42,false),(69,false),(121,false)]
theorem der_138460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138460 :=
  CNF.rup_sound cl_138460 [cl_126069,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126069 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_138461 : CNF.NClause := [(914,true),(905,false),(74,false),(926,true),(66,false),(912,true),(82,false),(37,true)]
theorem der_138461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138461 :=
  CNF.rup_sound cl_138461 [cl_130403,cl_115994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130403 v h) (hints_cons _ _ _ (der_115994 v h) (by intro d hd; cases hd)))
def cl_138462 : CNF.NClause := [(911,true),(913,true),(78,false),(72,false),(912,false),(44,true),(137,true),(65,false)]
theorem der_138462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138462 :=
  CNF.rup_sound cl_138462 [cl_123712,cl_112726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123712 v h) (hints_cons _ _ _ (der_112726 v h) (by intro d hd; cases hd)))
def cl_138463 : CNF.NClause := [(923,false),(55,true),(915,true),(91,false),(928,true),(76,false),(63,false),(906,true)]
theorem der_138463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138463 :=
  CNF.rup_sound cl_138463 [cl_126497,cl_62077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126497 v h) (hints_cons _ _ _ (der_62077 v h) (by intro d hd; cases hd)))
def cl_138464 : CNF.NClause := [(147,false),(17,false),(82,false),(120,true),(80,false),(7,false),(73,false),(71,false)]
theorem der_138464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138464 :=
  CNF.rup_sound cl_138464 [cl_126442,cl_29842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126442 v h) (hints_cons _ _ _ (der_29842 v h) (by intro d hd; cases hd)))
def cl_138465 : CNF.NClause := [(39,false),(136,false),(150,true),(130,false),(151,true),(152,false),(42,false),(137,false)]
theorem der_138465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138465 :=
  CNF.rup_sound cl_138465 [cl_125045,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125045 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_138466 : CNF.NClause := [(142,false),(121,false),(137,false),(141,false),(148,false),(42,false),(69,false),(97,false)]
theorem der_138466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138466 :=
  CNF.rup_sound cl_138466 [cl_126133,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126133 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_138468 : CNF.NClause := [(103,false),(112,false),(126,false),(116,false),(128,false),(43,false),(122,false),(64,false)]
theorem der_138468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138468 :=
  CNF.rup_sound cl_138468 [cl_126839,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126839 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138469 : CNF.NClause := [(104,false),(79,false),(150,false),(115,false),(121,false),(130,false),(59,false),(112,false)]
theorem der_138469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138469 :=
  CNF.rup_sound cl_138469 [cl_129536,cl_15791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129536 v h) (hints_cons _ _ _ (der_15791 v h) (by intro d hd; cases hd)))
def cl_138470 : CNF.NClause := [(58,false),(142,false),(45,false),(53,false),(150,false),(102,false),(83,false),(42,false)]
theorem der_138470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138470 :=
  CNF.rup_sound cl_138470 [cl_129102,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129102 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138471 : CNF.NClause := [(38,true),(17,false),(131,true),(7,false),(80,false),(73,false),(82,false),(71,false)]
theorem der_138471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138471 :=
  CNF.rup_sound cl_138471 [cl_125797,cl_29842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125797 v h) (hints_cons _ _ _ (der_29842 v h) (by intro d hd; cases hd)))
def cl_138472 : CNF.NClause := [(121,false),(115,false),(141,false),(142,false),(28,false),(150,false),(59,false),(133,false)]
theorem der_138472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138472 :=
  CNF.rup_sound cl_138472 [cl_131090,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131090 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_138473 : CNF.NClause := [(57,false),(94,false),(145,false),(82,false),(59,false),(133,false),(37,false),(42,false)]
theorem der_138473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138473 :=
  CNF.rup_sound cl_138473 [cl_131437,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131437 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_138474 : CNF.NClause := [(113,false),(153,false),(135,true),(136,true),(121,false),(138,true),(39,false),(137,false)]
theorem der_138474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138474 :=
  CNF.rup_sound cl_138474 [cl_131920,cl_126491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131920 v h) (hints_cons _ _ _ (der_126491 v h) (by intro d hd; cases hd)))
def cl_138475 : CNF.NClause := [(94,false),(111,false),(74,false),(144,false),(134,false),(55,false),(122,false),(115,false)]
theorem der_138475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138475 :=
  CNF.rup_sound cl_138475 [cl_132415,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132415 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138477 : CNF.NClause := [(920,false),(52,true),(79,false),(66,false),(904,true),(926,true),(918,true),(73,false)]
theorem der_138477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138477 :=
  CNF.rup_sound cl_138477 [cl_133325,cl_105706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133325 v h) (hints_cons _ _ _ (der_105706 v h) (by intro d hd; cases hd)))
def cl_138478 : CNF.NClause := [(141,false),(126,false),(69,false),(137,false),(128,false),(34,false),(45,false),(32,false)]
theorem der_138478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138478 :=
  CNF.rup_sound cl_138478 [cl_133586,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133586 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_138479 : CNF.NClause := [(122,false),(126,false),(134,false),(43,false),(116,false),(139,false),(128,false),(64,false)]
theorem der_138479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138479 :=
  CNF.rup_sound cl_138479 [cl_133685,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133685 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138480 : CNF.NClause := [(60,false),(44,false),(134,false),(74,false),(136,false),(144,false),(148,false),(40,false)]
theorem der_138480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138480 :=
  CNF.rup_sound cl_138480 [cl_134479,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134479 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138481 : CNF.NClause := [(35,false),(4,false),(118,false),(130,false),(99,false),(104,false),(114,false),(148,false)]
theorem der_138481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138481 :=
  CNF.rup_sound cl_138481 [cl_134599,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134599 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138482 : CNF.NClause := [(55,false),(130,false),(80,false),(146,false),(39,false),(144,false),(81,false),(49,false)]
theorem der_138482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138482 :=
  CNF.rup_sound cl_138482 [cl_134833,cl_107181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134833 v h) (hints_cons _ _ _ (der_107181 v h) (by intro d hd; cases hd)))
def cl_138483 : CNF.NClause := [(115,true),(9,false),(151,true),(126,false),(130,true),(139,false),(146,true),(55,false)]
theorem der_138483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138483 :=
  CNF.rup_sound cl_138483 [cl_134875,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134875 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_138484 : CNF.NClause := [(125,false),(48,false),(100,false),(52,false),(134,false),(75,false),(144,false),(128,false)]
theorem der_138484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138484 :=
  CNF.rup_sound cl_138484 [cl_135511,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135511 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_138485 : CNF.NClause := [(40,false),(126,false),(59,false),(50,false),(95,false),(52,false),(128,false),(64,false)]
theorem der_138485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138485 :=
  CNF.rup_sound cl_138485 [cl_135519,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135519 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138486 : CNF.NClause := [(114,false),(126,false),(36,false),(125,false),(123,false),(133,false),(131,true),(145,false)]
theorem der_138486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138486 :=
  CNF.rup_sound cl_138486 [cl_135694,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135694 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_138487 : CNF.NClause := [(60,false),(109,false),(52,false),(152,false),(77,false),(133,false),(141,false),(146,false)]
theorem der_138487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138487 :=
  CNF.rup_sound cl_138487 [cl_135887,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135887 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138488 : CNF.NClause := [(36,false),(141,false),(146,false),(52,false),(137,false),(39,false),(53,false),(85,false)]
theorem der_138488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138488 :=
  CNF.rup_sound cl_138488 [cl_135995,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135995 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_138489 : CNF.NClause := [(99,false),(113,false),(39,false),(125,false),(110,false),(121,false),(127,false),(85,false)]
theorem der_138489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138489 :=
  CNF.rup_sound cl_138489 [cl_136630,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136630 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_138490 : CNF.NClause := [(97,false),(41,false),(32,false),(137,false),(129,false),(82,false),(118,false),(133,false)]
theorem der_138490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138490 :=
  CNF.rup_sound cl_138490 [cl_136883,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136883 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138491 : CNF.NClause := [(143,true),(48,true),(142,false),(84,false),(138,false),(85,false),(21,false),(140,true)]
theorem der_138491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138491 :=
  CNF.rup_sound cl_138491 [cl_136949,cl_57480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136949 v h) (hints_cons _ _ _ (der_57480 v h) (by intro d hd; cases hd)))
def cl_138492 : CNF.NClause := [(138,false),(71,false),(80,false),(82,false),(7,false),(73,false),(64,false),(120,true)]
theorem der_138492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138492 :=
  CNF.rup_sound cl_138492 [cl_137947,cl_133919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137947 v h) (hints_cons _ _ _ (der_133919 v h) (by intro d hd; cases hd)))
def cl_138495 : CNF.NClause := [(151,false),(140,false),(59,false),(77,false),(121,false),(104,false),(150,true),(101,false),(112,false)]
theorem der_138495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138495 :=
  CNF.rup_sound cl_138495 [cl_107583,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107583 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_138497 : CNF.NClause := [(1075,true),(1057,true),(1071,true),(1082,true),(1076,true),(1060,true),(1073,true),(1077,true),(63,true)]
theorem der_138497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138497 :=
  CNF.rup_sound cl_138497 [cl_73294,cl_137964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73294 v h) (hints_cons _ _ _ (der_137964 v h) (by intro d hd; cases hd)))
def cl_138501 : CNF.NClause := [(130,false),(37,true),(66,false),(128,true),(152,true),(144,true),(140,true),(132,true),(151,false)]
theorem der_138501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138501 :=
  CNF.rup_sound cl_138501 [cl_107591,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107591 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_138502 : CNF.NClause := [(46,true),(125,true),(148,true),(133,true),(151,true),(141,true),(131,true),(139,false),(130,false)]
theorem der_138502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138502 :=
  CNF.rup_sound cl_138502 [cl_107592,cl_58211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107592 v h) (hints_cons _ _ _ (der_58211 v h) (by intro d hd; cases hd)))
def cl_138503 : CNF.NClause := [(109,false),(103,false),(44,false),(144,false),(119,false),(86,false),(96,false),(129,false),(71,false)]
theorem der_138503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138503 :=
  CNF.rup_sound cl_138503 [cl_107593,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107593 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_138504 : CNF.NClause := [(103,false),(117,false),(139,false),(94,false),(45,false),(151,false),(144,false),(68,false),(71,false)]
theorem der_138504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138504 :=
  CNF.rup_sound cl_138504 [cl_107594,cl_132993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107594 v h) (hints_cons _ _ _ (der_132993 v h) (by intro d hd; cases hd)))
def cl_138505 : CNF.NClause := [(104,false),(126,false),(108,false),(96,false),(49,false),(122,false),(131,true),(86,false),(125,false)]
theorem der_138505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138505 :=
  CNF.rup_sound cl_138505 [cl_107595,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107595 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138507 : CNF.NClause := [(114,false),(123,false),(125,false),(116,false),(131,true),(84,false),(126,false),(113,false),(36,false)]
theorem der_138507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138507 :=
  CNF.rup_sound cl_138507 [cl_107597,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107597 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_138508 : CNF.NClause := [(107,false),(146,false),(94,false),(135,false),(122,false),(80,false),(55,false),(115,false),(83,false)]
theorem der_138508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138508 :=
  CNF.rup_sound cl_138508 [cl_107598,cl_79623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107598 v h) (hints_cons _ _ _ (der_79623 v h) (by intro d hd; cases hd)))
def cl_138509 : CNF.NClause := [(106,false),(41,false),(123,false),(125,false),(131,true),(103,false),(126,false),(84,false),(104,false)]
theorem der_138509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138509 :=
  CNF.rup_sound cl_138509 [cl_107599,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107599 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_138510 : CNF.NClause := [(112,false),(131,true),(74,false),(127,false),(93,false),(121,false),(59,false),(104,false),(126,false)]
theorem der_138510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138510 :=
  CNF.rup_sound cl_138510 [cl_107600,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107600 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138512 : CNF.NClause := [(104,false),(100,false),(18,false),(122,false),(85,false),(139,false),(96,false),(49,false),(129,false)]
theorem der_138512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138512 :=
  CNF.rup_sound cl_138512 [cl_107601,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107601 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138513 : CNF.NClause := [(94,false),(134,false),(128,false),(75,false),(35,false),(139,false),(118,false),(114,false),(99,false)]
theorem der_138513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138513 :=
  CNF.rup_sound cl_138513 [cl_107602,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107602 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_138514 : CNF.NClause := [(126,false),(125,false),(86,false),(113,false),(131,true),(99,false),(121,false),(96,false),(39,false)]
theorem der_138514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138514 :=
  CNF.rup_sound cl_138514 [cl_107604,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107604 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138516 : CNF.NClause := [(914,true),(919,false),(903,true),(917,true),(911,true),(916,true),(74,true),(907,true),(909,true)]
theorem der_138516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138516 :=
  CNF.rup_sound cl_138516 [cl_106476,cl_137958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106476 v h) (hints_cons _ _ _ (der_137958 v h) (by intro d hd; cases hd)))
def cl_138517 : CNF.NClause := [(118,false),(100,false),(73,false),(152,false),(84,false),(105,false),(132,false),(33,false),(95,false)]
theorem der_138517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138517 :=
  CNF.rup_sound cl_138517 [cl_107609,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107609 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_138518 : CNF.NClause := [(97,false),(101,false),(37,false),(84,false),(129,false),(105,false),(86,false),(122,false),(139,false)]
theorem der_138518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138518 :=
  CNF.rup_sound cl_138518 [cl_107610,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107610 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138519 : CNF.NClause := [(126,false),(121,false),(127,false),(112,false),(64,false),(59,false),(85,false),(93,false),(104,false)]
theorem der_138519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138519 :=
  CNF.rup_sound cl_138519 [cl_107611,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107611 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138520 : CNF.NClause := [(105,false),(116,false),(79,false),(71,false),(94,false),(121,false),(50,false),(144,false),(139,false)]
theorem der_138520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138520 :=
  CNF.rup_sound cl_138520 [cl_107615,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107615 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_138521 : CNF.NClause := [(96,false),(118,false),(111,false),(106,false),(144,false),(34,false),(129,false),(86,false),(128,false)]
theorem der_138521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138521 :=
  CNF.rup_sound cl_138521 [cl_107618,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107618 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_138522 : CNF.NClause := [(121,false),(105,false),(94,false),(108,false),(50,false),(137,false),(145,false),(67,false),(73,false)]
theorem der_138522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138522 :=
  CNF.rup_sound cl_138522 [cl_107620,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107620 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_138523 : CNF.NClause := [(137,false),(145,false),(67,false),(73,false),(101,false),(117,false),(120,false),(45,false),(94,false)]
theorem der_138523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138523 :=
  CNF.rup_sound cl_138523 [cl_107621,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107621 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_138524 : CNF.NClause := [(129,true),(121,false),(99,false),(133,false),(131,true),(107,false),(110,false),(137,false),(39,false)]
theorem der_138524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138524 :=
  CNF.rup_sound cl_138524 [cl_98939,cl_126491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98939 v h) (hints_cons _ _ _ (der_126491 v h) (by intro d hd; cases hd)))
def cl_138525 : CNF.NClause := [(49,false),(132,false),(134,false),(122,false),(135,false),(138,false),(117,false),(139,false),(142,false)]
theorem der_138525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138525 :=
  CNF.rup_sound cl_138525 [cl_107622,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107622 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138526 : CNF.NClause := [(117,false),(143,false),(49,false),(69,false),(122,false),(96,false),(135,false),(85,false),(104,false)]
theorem der_138526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138526 :=
  CNF.rup_sound cl_138526 [cl_107623,cl_107208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107623 v h) (hints_cons _ _ _ (der_107208 v h) (by intro d hd; cases hd)))
def cl_138527 : CNF.NClause := [(117,false),(127,false),(120,false),(45,false),(138,false),(83,false),(103,false),(128,false),(110,false)]
theorem der_138527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138527 :=
  CNF.rup_sound cl_138527 [cl_107624,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107624 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138528 : CNF.NClause := [(103,false),(122,false),(127,false),(126,false),(99,false),(85,false),(112,false),(84,false),(43,false)]
theorem der_138528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138528 :=
  CNF.rup_sound cl_138528 [cl_107625,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107625 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_138529 : CNF.NClause := [(100,false),(127,false),(138,false),(128,false),(121,false),(42,false),(97,false),(83,false),(103,false)]
theorem der_138529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138529 :=
  CNF.rup_sound cl_138529 [cl_107626,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107626 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138530 : CNF.NClause := [(117,false),(134,false),(122,false),(96,false),(49,false),(139,false),(73,false),(100,false),(75,false)]
theorem der_138530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138530 :=
  CNF.rup_sound cl_138530 [cl_107627,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107627 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_138531 : CNF.NClause := [(909,true),(88,true),(926,true),(911,true),(915,true),(907,true),(913,true),(923,true),(905,true)]
theorem der_138531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138531 :=
  CNF.rup_sound cl_138531 [cl_107629,cl_115969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107629 v h) (hints_cons _ _ _ (der_115969 v h) (by intro d hd; cases hd)))
def cl_138532 : CNF.NClause := [(94,false),(115,false),(139,false),(122,false),(134,false),(55,false),(98,false),(74,false),(73,false)]
theorem der_138532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138532 :=
  CNF.rup_sound cl_138532 [cl_107631,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107631 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138533 : CNF.NClause := [(47,false),(125,false),(41,false),(65,false),(128,false),(138,false),(23,false),(51,false),(67,false)]
theorem der_138533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138533 :=
  CNF.rup_sound cl_138533 [cl_107632,cl_115997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107632 v h) (hints_cons _ _ _ (der_115997 v h) (by intro d hd; cases hd)))
def cl_138534 : CNF.NClause := [(57,false),(75,false),(114,false),(110,false),(127,false),(122,false),(138,false),(93,false),(125,false)]
theorem der_138534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138534 :=
  CNF.rup_sound cl_138534 [cl_107633,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107633 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138535 : CNF.NClause := [(138,false),(147,false),(65,false),(43,false),(95,false),(99,false),(122,false),(116,false),(42,true)]
theorem der_138535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138535 :=
  CNF.rup_sound cl_138535 [cl_107634,cl_81199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107634 v h) (hints_cons _ _ _ (der_81199 v h) (by intro d hd; cases hd)))
def cl_138536 : CNF.NClause := [(121,false),(50,false),(74,false),(134,false),(75,false),(94,false),(116,false),(139,false),(102,false)]
theorem der_138536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138536 :=
  CNF.rup_sound cl_138536 [cl_107637,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107637 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_138537 : CNF.NClause := [(116,false),(134,false),(120,false),(100,false),(58,false),(139,false),(93,false),(73,false),(75,false)]
theorem der_138537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138537 :=
  CNF.rup_sound cl_138537 [cl_107639,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107639 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_138539 : CNF.NClause := [(48,true),(141,false),(88,false),(142,true),(146,false),(85,false),(74,false),(138,false),(17,false)]
theorem der_138539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138539 :=
  CNF.rup_sound cl_138539 [cl_103831,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103831 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_138540 : CNF.NClause := [(27,false),(141,true),(143,true),(88,false),(138,false),(85,false),(84,false),(71,false),(140,true)]
theorem der_138540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138540 :=
  CNF.rup_sound cl_138540 [cl_109027,cl_56745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109027 v h) (hints_cons _ _ _ (der_56745 v h) (by intro d hd; cases hd)))
def cl_138542 : CNF.NClause := [(111,false),(98,false),(138,false),(94,false),(122,false),(126,false),(55,false),(125,false),(76,false)]
theorem der_138542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138542 :=
  CNF.rup_sound cl_138542 [cl_107641,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107641 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_138543 : CNF.NClause := [(104,false),(99,false),(79,false),(150,false),(83,false),(130,false),(94,false),(35,false),(118,false)]
theorem der_138543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138543 :=
  CNF.rup_sound cl_138543 [cl_108766,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108766 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138544 : CNF.NClause := [(35,false),(4,false),(148,false),(99,false),(104,false),(80,false),(130,false),(118,false),(114,false)]
theorem der_138544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138544 :=
  CNF.rup_sound cl_138544 [cl_109847,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109847 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138545 : CNF.NClause := [(41,false),(97,false),(111,false),(42,false),(114,false),(76,false),(121,false),(14,true),(144,false)]
theorem der_138545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138545 :=
  CNF.rup_sound cl_138545 [cl_109110,cl_115998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109110 v h) (hints_cons _ _ _ (der_115998 v h) (by intro d hd; cases hd)))
def cl_138546 : CNF.NClause := [(137,false),(44,true),(139,true),(125,true),(148,true),(131,true),(130,false),(140,true),(127,true)]
theorem der_138546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138546 :=
  CNF.rup_sound cl_138546 [cl_104095,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104095 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_138547 : CNF.NClause := [(150,false),(130,false),(99,false),(96,false),(121,false),(107,false),(71,false),(39,false),(83,false)]
theorem der_138547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138547 :=
  CNF.rup_sound cl_138547 [cl_109805,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109805 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138548 : CNF.NClause := [(132,false),(138,false),(142,true),(127,true),(137,true),(95,false),(106,false),(53,false),(109,false)]
theorem der_138548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138548 :=
  CNF.rup_sound cl_138548 [cl_104383,cl_107229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104383 v h) (hints_cons _ _ _ (der_107229 v h) (by intro d hd; cases hd)))
def cl_138549 : CNF.NClause := [(121,false),(129,true),(107,false),(133,false),(39,false),(96,false),(131,true),(145,false),(99,false)]
theorem der_138549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138549 :=
  CNF.rup_sound cl_138549 [cl_107649,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107649 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_138550 : CNF.NClause := [(36,false),(117,false),(141,false),(116,false),(113,false),(77,false),(146,false),(123,false),(137,false)]
theorem der_138550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138550 :=
  CNF.rup_sound cl_138550 [cl_106530,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106530 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138551 : CNF.NClause := [(103,false),(146,false),(130,false),(133,true),(116,false),(43,false),(131,true),(129,true),(112,false)]
theorem der_138551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138551 :=
  CNF.rup_sound cl_138551 [cl_102977,cl_115804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102977 v h) (hints_cons _ _ _ (der_115804 v h) (by intro d hd; cases hd)))
def cl_138552 : CNF.NClause := [(109,false),(123,false),(77,false),(141,false),(145,false),(138,false),(46,false),(111,false),(112,false)]
theorem der_138552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138552 :=
  CNF.rup_sound cl_138552 [cl_107645,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107645 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_138553 : CNF.NClause := [(141,false),(99,false),(96,false),(121,false),(145,false),(73,false),(113,false),(39,false),(77,false)]
theorem der_138553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138553 :=
  CNF.rup_sound cl_138553 [cl_109634,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109634 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138554 : CNF.NClause := [(106,false),(34,false),(63,false),(136,false),(148,false),(96,false),(101,false),(80,false),(118,false)]
theorem der_138554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138554 :=
  CNF.rup_sound cl_138554 [cl_109901,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109901 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138555 : CNF.NClause := [(118,false),(101,false),(150,false),(96,false),(83,false),(116,false),(148,false),(79,false),(34,false)]
theorem der_138555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138555 :=
  CNF.rup_sound cl_138555 [cl_109598,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109598 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138558 : CNF.NClause := [(95,false),(38,false),(111,false),(145,false),(102,false),(133,false),(120,false),(69,false),(138,false)]
theorem der_138558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138558 :=
  CNF.rup_sound cl_138558 [cl_107643,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107643 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_138559 : CNF.NClause := [(38,false),(129,false),(134,false),(42,false),(53,false),(86,false),(50,false),(82,false),(107,false)]
theorem der_138559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138559 :=
  CNF.rup_sound cl_138559 [cl_114975,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114975 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138560 : CNF.NClause := [(143,false),(129,false),(86,false),(122,false),(83,false),(134,false),(49,false),(100,false),(39,false)]
theorem der_138560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138560 :=
  CNF.rup_sound cl_138560 [cl_115447,cl_79625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_115447 v h) (hints_cons _ _ _ (der_79625 v h) (by intro d hd; cases hd)))
def cl_138562 : CNF.NClause := [(57,false),(144,false),(50,false),(49,false),(134,false),(75,false),(43,false),(74,false),(107,false)]
theorem der_138562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138562 :=
  CNF.rup_sound cl_138562 [cl_114312,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114312 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_138563 : CNF.NClause := [(54,false),(47,false),(59,false),(133,false),(145,false),(63,false),(110,false),(73,false),(50,false)]
theorem der_138563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138563 :=
  CNF.rup_sound cl_138563 [cl_112903,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112903 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138564 : CNF.NClause := [(113,false),(120,false),(151,true),(152,false),(102,false),(150,true),(38,false),(141,false),(90,false)]
theorem der_138564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138564 :=
  CNF.rup_sound cl_138564 [cl_114582,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114582 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138565 : CNF.NClause := [(120,false),(54,false),(145,false),(138,true),(143,false),(114,false),(148,true),(128,true),(39,false)]
theorem der_138565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138565 :=
  CNF.rup_sound cl_138565 [cl_115150,cl_79625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_115150 v h) (hints_cons _ _ _ (der_79625 v h) (by intro d hd; cases hd)))
def cl_138566 : CNF.NClause := [(45,false),(134,false),(75,false),(74,false),(120,false),(144,false),(117,false),(94,false),(110,false)]
theorem der_138566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138566 :=
  CNF.rup_sound cl_138566 [cl_111714,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111714 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_138568 : CNF.NClause := [(38,false),(141,false),(120,false),(86,false),(113,false),(60,false),(102,false),(80,false),(104,false)]
theorem der_138568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138568 :=
  CNF.rup_sound cl_138568 [cl_114292,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114292 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138571 : CNF.NClause := [(38,false),(47,false),(45,false),(133,false),(42,false),(77,false),(141,false),(70,false),(39,false)]
theorem der_138571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138571 :=
  CNF.rup_sound cl_138571 [cl_113615,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113615 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_138574 : CNF.NClause := [(151,false),(138,false),(50,false),(134,false),(75,false),(108,false),(144,false),(74,false),(121,false)]
theorem der_138574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138574 :=
  CNF.rup_sound cl_138574 [cl_116692,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116692 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_138575 : CNF.NClause := [(33,false),(118,false),(95,false),(115,false),(74,false),(76,false),(144,false),(134,false),(110,false)]
theorem der_138575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138575 :=
  CNF.rup_sound cl_138575 [cl_113801,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113801 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138576 : CNF.NClause := [(118,false),(101,false),(75,false),(116,false),(148,false),(34,false),(150,false),(96,false),(79,false)]
theorem der_138576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138576 :=
  CNF.rup_sound cl_138576 [cl_116588,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116588 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138579 : CNF.NClause := [(118,false),(109,false),(150,false),(83,false),(94,false),(99,false),(79,false),(142,false),(35,false)]
theorem der_138579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138579 :=
  CNF.rup_sound cl_138579 [cl_110190,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110190 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138580 : CNF.NClause := [(121,false),(142,false),(114,false),(143,true),(138,false),(12,false),(141,true),(42,false),(139,true)]
theorem der_138580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138580 :=
  CNF.rup_sound cl_138580 [cl_113380,cl_128232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113380 v h) (hints_cons _ _ _ (der_128232 v h) (by intro d hd; cases hd)))
def cl_138581 : CNF.NClause := [(151,false),(138,false),(114,false),(118,false),(99,false),(152,true),(150,true),(145,false),(35,false)]
theorem der_138581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138581 :=
  CNF.rup_sound cl_138581 [cl_110752,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110752 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_138582 : CNF.NClause := [(89,false),(142,true),(145,false),(143,true),(84,false),(71,false),(29,false),(141,true),(86,false)]
theorem der_138582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138582 :=
  CNF.rup_sound cl_138582 [cl_115124,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_115124 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_138584 : CNF.NClause := [(38,false),(45,false),(42,false),(141,false),(83,false),(133,false),(77,false),(50,false),(39,false)]
theorem der_138584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138584 :=
  CNF.rup_sound cl_138584 [cl_112423,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112423 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_138585 : CNF.NClause := [(106,true),(20,false),(130,false),(143,true),(147,true),(153,true),(76,false),(53,false),(127,false)]
theorem der_138585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138585 :=
  CNF.rup_sound cl_138585 [cl_113993,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113993 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138586 : CNF.NClause := [(20,false),(105,true),(153,true),(76,false),(130,true),(143,false),(140,false),(3,false),(50,false)]
theorem der_138586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138586 :=
  CNF.rup_sound cl_138586 [cl_116585,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116585 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138589 : CNF.NClause := [(101,false),(129,false),(93,false),(121,false),(82,false),(112,false),(134,false),(86,false),(59,false)]
theorem der_138589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138589 :=
  CNF.rup_sound cl_138589 [cl_113249,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113249 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138590 : CNF.NClause := [(142,false),(50,false),(121,false),(82,false),(130,false),(86,false),(145,false),(133,false),(102,false)]
theorem der_138590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138590 :=
  CNF.rup_sound cl_138590 [cl_115531,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_115531 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_138593 : CNF.NClause := [(117,false),(108,false),(96,false),(49,false),(73,false),(145,false),(82,false),(122,false),(133,false)]
theorem der_138593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138593 :=
  CNF.rup_sound cl_138593 [cl_116007,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116007 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_138595 : CNF.NClause := [(45,false),(38,false),(50,false),(59,false),(136,false),(47,false),(84,false),(63,false),(148,false)]
theorem der_138595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138595 :=
  CNF.rup_sound cl_138595 [cl_116701,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116701 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_138596 : CNF.NClause := [(131,false),(147,false),(94,false),(83,false),(65,false),(118,false),(99,false),(109,false),(35,false)]
theorem der_138596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138596 :=
  CNF.rup_sound cl_138596 [cl_110163,cl_76537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110163 v h) (hints_cons _ _ _ (der_76537 v h) (by intro d hd; cases hd)))
def cl_138597 : CNF.NClause := [(129,false),(55,true),(138,true),(147,true),(143,false),(128,true),(133,true),(141,true),(135,true)]
theorem der_138597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138597 :=
  CNF.rup_sound cl_138597 [cl_116967,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116967 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_138599 : CNF.NClause := [(153,false),(152,false),(39,false),(148,false),(80,false),(143,false),(135,true),(130,false),(145,false)]
theorem der_138599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138599 :=
  CNF.rup_sound cl_138599 [cl_117189,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117189 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138600 : CNF.NClause := [(114,false),(57,false),(102,false),(153,false),(110,false),(133,false),(82,false),(122,false),(63,false)]
theorem der_138600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138600 :=
  CNF.rup_sound cl_138600 [cl_117539,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117539 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_138601 : CNF.NClause := [(121,false),(115,false),(134,false),(144,false),(76,false),(59,false),(93,false),(112,false),(74,false)]
theorem der_138601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138601 :=
  CNF.rup_sound cl_138601 [cl_121925,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121925 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138602 : CNF.NClause := [(144,false),(40,false),(39,false),(94,false),(74,false),(70,false),(119,false),(112,false),(134,false)]
theorem der_138602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138602 :=
  CNF.rup_sound cl_138602 [cl_118584,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118584 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138604 : CNF.NClause := [(115,true),(129,false),(82,false),(130,true),(134,false),(137,false),(143,true),(126,true),(147,true)]
theorem der_138604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138604 :=
  CNF.rup_sound cl_138604 [cl_123669,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123669 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138605 : CNF.NClause := [(39,false),(143,false),(142,false),(43,true),(137,true),(138,true),(135,false),(129,false),(122,false)]
theorem der_138605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138605 :=
  CNF.rup_sound cl_138605 [cl_117876,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117876 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_138608 : CNF.NClause := [(39,false),(128,false),(105,false),(131,true),(146,true),(42,false),(148,false),(141,true),(126,false)]
theorem der_138608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138608 :=
  CNF.rup_sound cl_138608 [cl_118186,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118186 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_138610 : CNF.NClause := [(917,false),(21,true),(91,false),(86,false),(65,false),(49,true),(915,true),(69,false),(914,true)]
theorem der_138610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138610 :=
  CNF.rup_sound cl_138610 [cl_123662,cl_105801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123662 v h) (hints_cons _ _ _ (der_105801 v h) (by intro d hd; cases hd)))
def cl_138612 : CNF.NClause := [(109,false),(134,false),(121,false),(144,false),(74,false),(117,false),(95,false),(75,false),(53,false)]
theorem der_138612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138612 :=
  CNF.rup_sound cl_138612 [cl_120042,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120042 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_138613 : CNF.NClause := [(101,true),(138,false),(146,true),(136,true),(127,false),(80,false),(85,false),(141,false),(48,false)]
theorem der_138613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138613 :=
  CNF.rup_sound cl_138613 [cl_118971,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118971 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_138617 : CNF.NClause := [(1063,false),(1066,true),(75,false),(82,false),(1069,true),(133,true),(69,false),(40,true),(1077,true)]
theorem der_138617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138617 :=
  CNF.rup_sound cl_138617 [cl_122595,cl_137964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122595 v h) (hints_cons _ _ _ (der_137964 v h) (by intro d hd; cases hd)))
def cl_138619 : CNF.NClause := [(125,false),(118,true),(80,false),(65,false),(127,false),(75,false),(71,false),(76,false),(70,false)]
theorem der_138619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138619 :=
  CNF.rup_sound cl_138619 [cl_123441,cl_56933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123441 v h) (hints_cons _ _ _ (der_56933 v h) (by intro d hd; cases hd)))
def cl_138620 : CNF.NClause := [(57,false),(130,false),(152,false),(85,false),(39,false),(137,false),(64,false),(12,false),(145,false)]
theorem der_138620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138620 :=
  CNF.rup_sound cl_138620 [cl_121883,cl_62596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121883 v h) (hints_cons _ _ _ (der_62596 v h) (by intro d hd; cases hd)))
def cl_138621 : CNF.NClause := [(53,false),(39,false),(150,false),(141,false),(151,true),(152,true),(50,false),(71,false),(148,false)]
theorem der_138621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138621 :=
  CNF.rup_sound cl_138621 [cl_119956,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119956 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138623 : CNF.NClause := [(54,false),(47,false),(141,false),(59,false),(133,false),(70,false),(77,false),(107,false),(53,false)]
theorem der_138623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138623 :=
  CNF.rup_sound cl_138623 [cl_121197,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121197 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_138625 : CNF.NClause := [(60,false),(143,false),(82,false),(84,false),(113,false),(44,false),(129,false),(135,false),(134,false)]
theorem der_138625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138625 :=
  CNF.rup_sound cl_138625 [cl_117660,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117660 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138626 : CNF.NClause := [(121,false),(151,false),(82,false),(117,false),(148,false),(137,false),(53,false),(136,false),(133,false)]
theorem der_138626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138626 :=
  CNF.rup_sound cl_138626 [cl_120927,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120927 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138627 : CNF.NClause := [(130,false),(58,false),(79,false),(150,false),(120,false),(100,false),(107,false),(116,false),(71,false)]
theorem der_138627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138627 :=
  CNF.rup_sound cl_138627 [cl_118432,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118432 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138628 : CNF.NClause := [(109,false),(58,false),(71,false),(120,false),(142,false),(150,false),(79,false),(116,false),(107,false)]
theorem der_138628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138628 :=
  CNF.rup_sound cl_138628 [cl_117358,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117358 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138631 : CNF.NClause := [(131,false),(138,false),(140,true),(141,true),(84,false),(88,false),(142,true),(85,false),(139,true)]
theorem der_138631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138631 :=
  CNF.rup_sound cl_138631 [cl_122307,cl_56745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122307 v h) (hints_cons _ _ _ (der_56745 v h) (by intro d hd; cases hd)))
def cl_138632 : CNF.NClause := [(37,false),(148,true),(146,false),(99,false),(141,false),(144,true),(140,false),(137,false),(39,false)]
theorem der_138632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138632 :=
  CNF.rup_sound cl_138632 [cl_120182,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120182 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138633 : CNF.NClause := [(9,false),(125,false),(50,false),(39,false),(48,false),(63,false),(75,false),(59,false),(126,false)]
theorem der_138633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138633 :=
  CNF.rup_sound cl_138633 [cl_119931,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119931 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_138634 : CNF.NClause := [(107,false),(108,false),(95,false),(71,false),(119,false),(79,false),(150,false),(130,false),(48,false)]
theorem der_138634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138634 :=
  CNF.rup_sound cl_138634 [cl_119806,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119806 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138636 : CNF.NClause := [(95,false),(83,false),(108,false),(48,false),(129,false),(144,false),(107,false),(85,false),(119,false)]
theorem der_138636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138636 :=
  CNF.rup_sound cl_138636 [cl_119820,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119820 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138638 : CNF.NClause := [(54,false),(39,false),(130,false),(148,false),(53,false),(63,false),(84,false),(42,false),(59,false)]
theorem der_138638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138638 :=
  CNF.rup_sound cl_138638 [cl_125279,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125279 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_138639 : CNF.NClause := [(10,false),(141,true),(135,false),(16,false),(82,false),(150,true),(42,false),(2,false),(114,true)]
theorem der_138639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138639 :=
  CNF.rup_sound cl_138639 [cl_125077,cl_76584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125077 v h) (hints_cons _ _ _ (der_76584 v h) (by intro d hd; cases hd)))
def cl_138641 : CNF.NClause := [(917,true),(918,true),(70,false),(76,false),(12,false),(48,true),(914,true),(83,false),(916,false)]
theorem der_138641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138641 :=
  CNF.rup_sound cl_138641 [cl_129815,cl_107244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129815 v h) (hints_cons _ _ _ (der_107244 v h) (by intro d hd; cases hd)))
def cl_138642 : CNF.NClause := [(43,false),(102,false),(144,false),(76,false),(134,false),(48,false),(53,false),(74,false),(42,false)]
theorem der_138642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138642 :=
  CNF.rup_sound cl_138642 [cl_126873,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126873 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138643 : CNF.NClause := [(111,false),(140,false),(121,false),(129,false),(138,false),(66,false),(84,false),(144,false),(42,false)]
theorem der_138643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138643 :=
  CNF.rup_sound cl_138643 [cl_130139,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130139 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138644 : CNF.NClause := [(48,false),(44,false),(73,false),(100,false),(144,false),(52,false),(134,false),(60,false),(74,false)]
theorem der_138644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138644 :=
  CNF.rup_sound cl_138644 [cl_129087,cl_61991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129087 v h) (hints_cons _ _ _ (der_61991 v h) (by intro d hd; cases hd)))
def cl_138645 : CNF.NClause := [(95,false),(144,false),(109,false),(129,false),(53,false),(67,false),(106,false),(121,false),(68,false)]
theorem der_138645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138645 :=
  CNF.rup_sound cl_138645 [cl_127930,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127930 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_138648 : CNF.NClause := [(100,false),(111,false),(97,false),(129,false),(121,false),(82,false),(83,false),(134,false),(42,false)]
theorem der_138648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138648 :=
  CNF.rup_sound cl_138648 [cl_129946,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129946 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_138650 : CNF.NClause := [(43,false),(38,false),(53,false),(47,false),(129,false),(82,false),(134,false),(83,false),(42,false)]
theorem der_138650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138650 :=
  CNF.rup_sound cl_138650 [cl_130725,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130725 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_138651 : CNF.NClause := [(910,false),(76,true),(928,true),(905,true),(904,true),(10,true),(914,true),(902,true),(908,true)]
theorem der_138651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138651 :=
  CNF.rup_sound cl_138651 [cl_130399,cl_128236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130399 v h) (hints_cons _ _ _ (der_128236 v h) (by intro d hd; cases hd)))
def cl_138652 : CNF.NClause := [(138,false),(147,false),(99,false),(119,false),(6,false),(90,false),(153,false),(60,false),(111,false)]
theorem der_138652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138652 :=
  CNF.rup_sound cl_138652 [cl_129149,cl_56745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129149 v h) (hints_cons _ _ _ (der_56745 v h) (by intro d hd; cases hd)))
def cl_138653 : CNF.NClause := [(109,false),(97,false),(122,false),(37,false),(60,false),(80,false),(113,false),(68,false),(141,false)]
theorem der_138653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138653 :=
  CNF.rup_sound cl_138653 [cl_125966,cl_108024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125966 v h) (hints_cons _ _ _ (der_108024 v h) (by intro d hd; cases hd)))
def cl_138654 : CNF.NClause := [(106,true),(141,true),(139,true),(129,true),(128,true),(18,false),(135,false),(34,false),(140,false)]
theorem der_138654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138654 :=
  CNF.rup_sound cl_138654 [cl_130384,cl_85856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130384 v h) (hints_cons _ _ _ (der_85856 v h) (by intro d hd; cases hd)))
def cl_138657 : CNF.NClause := [(148,false),(55,true),(4,false),(153,true),(141,true),(144,false),(138,true),(127,true),(151,true)]
theorem der_138657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138657 :=
  CNF.rup_sound cl_138657 [cl_127375,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127375 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_138658 : CNF.NClause := [(48,false),(152,false),(151,true),(126,false),(90,false),(52,false),(24,false),(125,false),(121,false)]
theorem der_138658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138658 :=
  CNF.rup_sound cl_138658 [cl_130754,cl_79529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130754 v h) (hints_cons _ _ _ (der_79529 v h) (by intro d hd; cases hd)))
def cl_138659 : CNF.NClause := [(20,false),(17,false),(143,false),(37,false),(113,true),(132,true),(130,false),(128,true),(148,true)]
theorem der_138659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138659 :=
  CNF.rup_sound cl_138659 [cl_126583,cl_62857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126583 v h) (hints_cons _ _ _ (der_62857 v h) (by intro d hd; cases hd)))
def cl_138660 : CNF.NClause := [(146,false),(125,false),(102,false),(84,false),(39,false),(59,false),(42,false),(69,false),(33,false)]
theorem der_138660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138660 :=
  CNF.rup_sound cl_138660 [cl_124307,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124307 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_138663 : CNF.NClause := [(106,false),(58,false),(82,false),(37,false),(129,false),(134,false),(49,false),(83,false),(42,false)]
theorem der_138663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138663 :=
  CNF.rup_sound cl_138663 [cl_127888,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127888 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_138664 : CNF.NClause := [(103,false),(96,false),(102,false),(148,true),(143,true),(128,false),(44,false),(138,true),(126,false)]
theorem der_138664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138664 :=
  CNF.rup_sound cl_138664 [cl_128700,cl_79491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128700 v h) (hints_cons _ _ _ (der_79491 v h) (by intro d hd; cases hd)))
def cl_138665 : CNF.NClause := [(105,true),(125,true),(134,false),(131,true),(60,false),(150,false),(75,false),(90,false),(137,true)]
theorem der_138665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138665 :=
  CNF.rup_sound cl_138665 [cl_130894,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130894 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_138666 : CNF.NClause := [(33,false),(34,false),(151,false),(147,false),(148,false),(150,false),(50,false),(71,false),(83,false)]
theorem der_138666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138666 :=
  CNF.rup_sound cl_138666 [cl_131260,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131260 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_138667 : CNF.NClause := [(55,false),(116,false),(108,false),(105,false),(150,false),(121,false),(50,false),(71,false),(80,false)]
theorem der_138667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138667 :=
  CNF.rup_sound cl_138667 [cl_131302,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131302 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_138668 : CNF.NClause := [(121,false),(113,false),(136,true),(88,false),(138,true),(39,false),(99,false),(134,false),(135,true)]
theorem der_138668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138668 :=
  CNF.rup_sound cl_138668 [cl_131836,cl_126491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131836 v h) (hints_cons _ _ _ (der_126491 v h) (by intro d hd; cases hd)))
def cl_138670 : CNF.NClause := [(141,false),(117,false),(77,false),(96,false),(133,false),(70,false),(122,false),(49,false),(104,false)]
theorem der_138670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138670 :=
  CNF.rup_sound cl_138670 [cl_133363,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133363 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_138671 : CNF.NClause := [(141,false),(111,false),(122,false),(70,false),(98,false),(115,false),(133,false),(55,false),(77,false)]
theorem der_138671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138671 :=
  CNF.rup_sound cl_138671 [cl_133437,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133437 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_138674 : CNF.NClause := [(48,false),(133,false),(49,false),(44,false),(76,false),(128,false),(118,false),(63,false),(153,false)]
theorem der_138674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138674 :=
  CNF.rup_sound cl_138674 [cl_134133,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134133 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_138675 : CNF.NClause := [(44,false),(122,false),(127,false),(97,false),(133,false),(37,false),(69,false),(126,false),(64,false)]
theorem der_138675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138675 :=
  CNF.rup_sound cl_138675 [cl_134837,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134837 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_138676 : CNF.NClause := [(46,false),(135,true),(51,false),(130,false),(136,false),(148,false),(126,false),(145,true),(140,true)]
theorem der_138676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138676 :=
  CNF.rup_sound cl_138676 [cl_135174,cl_137960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135174 v h) (hints_cons _ _ _ (der_137960 v h) (by intro d hd; cases hd)))
def cl_138677 : CNF.NClause := [(100,false),(135,true),(123,false),(51,false),(128,false),(148,false),(130,false),(145,true),(140,true)]
theorem der_138677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138677 :=
  CNF.rup_sound cl_138677 [cl_135214,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135214 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138678 : CNF.NClause := [(60,false),(146,false),(130,false),(129,false),(77,false),(141,false),(52,false),(133,false),(139,false)]
theorem der_138678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138678 :=
  CNF.rup_sound cl_138678 [cl_135878,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135878 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138679 : CNF.NClause := [(59,false),(133,false),(84,false),(117,false),(52,false),(146,false),(109,false),(141,false),(77,false)]
theorem der_138679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138679 :=
  CNF.rup_sound cl_138679 [cl_135888,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135888 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138680 : CNF.NClause := [(33,false),(139,false),(146,false),(18,false),(130,false),(129,false),(97,false),(127,false),(73,false)]
theorem der_138680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138680 :=
  CNF.rup_sound cl_138680 [cl_136766,cl_79486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136766 v h) (hints_cons _ _ _ (der_79486 v h) (by intro d hd; cases hd)))
def cl_138681 : CNF.NClause := [(32,true),(146,false),(138,true),(142,true),(153,true),(129,true),(139,true),(145,false),(150,true)]
theorem der_138681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138681 :=
  CNF.rup_sound cl_138681 [cl_137479,cl_15788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137479 v h) (hints_cons _ _ _ (der_15788 v h) (by intro d hd; cases hd)))
def cl_138682 : CNF.NClause := [(136,false),(134,true),(53,false),(148,false),(138,true),(39,false),(135,true),(128,true),(145,false)]
theorem der_138682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138682 :=
  CNF.rup_sound cl_138682 [cl_137777,cl_107229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137777 v h) (hints_cons _ _ _ (der_107229 v h) (by intro d hd; cases hd)))
def cl_138690 : CNF.NClause := [(111,false),(119,false),(128,false),(60,false),(93,false),(131,true),(117,false),(74,false),(79,false),(126,false)]
theorem der_138690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138690 :=
  CNF.rup_sound cl_138690 [cl_107657,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107657 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_138691 : CNF.NClause := [(95,false),(83,false),(129,false),(84,false),(144,false),(107,false),(85,false),(119,false),(108,false),(48,false)]
theorem der_138691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138691 :=
  CNF.rup_sound cl_138691 [cl_107658,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107658 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138692 : CNF.NClause := [(151,false),(140,false),(141,true),(111,false),(68,false),(75,false),(55,false),(122,false),(94,false),(98,false)]
theorem der_138692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138692 :=
  CNF.rup_sound cl_138692 [cl_107659,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107659 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_138694 : CNF.NClause := [(71,true),(1056,false),(1073,true),(1060,true),(1066,true),(1068,true),(1057,true),(1055,true),(1076,true),(1082,true)]
theorem der_138694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138694 :=
  CNF.rup_sound cl_138694 [cl_79049,cl_138031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79049 v h) (hints_cons _ _ _ (der_138031 v h) (by intro d hd; cases hd)))
def cl_138696 : CNF.NClause := [(38,false),(111,false),(71,false),(95,false),(120,false),(104,false),(86,false),(129,false),(83,false),(144,false)]
theorem der_138696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138696 :=
  CNF.rup_sound cl_138696 [cl_107667,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107667 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_138697 : CNF.NClause := [(89,false),(142,true),(112,true),(137,true),(147,false),(65,false),(86,false),(71,false),(125,false),(132,true)]
theorem der_138697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138697 :=
  CNF.rup_sound cl_138697 [cl_88746,cl_63040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88746 v h) (hints_cons _ _ _ (der_63040 v h) (by intro d hd; cases hd)))
def cl_138699 : CNF.NClause := [(129,false),(112,false),(71,false),(70,false),(144,false),(93,false),(104,false),(59,false),(86,false),(121,false)]
theorem der_138699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138699 :=
  CNF.rup_sound cl_138699 [cl_107669,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107669 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138700 : CNF.NClause := [(35,false),(118,false),(129,false),(78,false),(139,false),(104,false),(86,false),(94,false),(99,false),(84,false)]
theorem der_138700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138700 :=
  CNF.rup_sound cl_138700 [cl_107673,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107673 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138701 : CNF.NClause := [(38,false),(98,false),(39,false),(71,false),(42,false),(129,false),(144,false),(83,false),(68,false),(59,false)]
theorem der_138701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138701 :=
  CNF.rup_sound cl_138701 [cl_107674,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107674 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138702 : CNF.NClause := [(109,false),(46,false),(123,false),(125,false),(75,false),(108,false),(110,false),(85,false),(127,false),(70,false)]
theorem der_138702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138702 :=
  CNF.rup_sound cl_138702 [cl_107675,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107675 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_138703 : CNF.NClause := [(103,false),(126,false),(104,false),(127,false),(84,false),(107,false),(85,false),(123,false),(75,false),(41,false)]
theorem der_138703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138703 :=
  CNF.rup_sound cl_138703 [cl_107677,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107677 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_138705 : CNF.NClause := [(109,false),(107,false),(74,false),(120,false),(100,false),(58,false),(152,false),(142,true),(141,true),(143,false)]
theorem der_138705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138705 :=
  CNF.rup_sound cl_138705 [cl_107679,cl_79625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107679 v h) (hints_cons _ _ _ (der_79625 v h) (by intro d hd; cases hd)))
def cl_138706 : CNF.NClause := [(142,false),(111,false),(93,false),(77,false),(105,false),(60,false),(85,false),(64,false),(136,false),(119,false)]
theorem der_138706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138706 :=
  CNF.rup_sound cl_138706 [cl_107680,cl_86128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107680 v h) (hints_cons _ _ _ (der_86128 v h) (by intro d hd; cases hd)))
def cl_138707 : CNF.NClause := [(115,false),(59,false),(121,false),(130,false),(64,false),(72,false),(136,false),(81,false),(93,false),(104,false)]
theorem der_138707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138707 :=
  CNF.rup_sound cl_138707 [cl_107681,cl_57205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107681 v h) (hints_cons _ _ _ (der_57205 v h) (by intro d hd; cases hd)))
def cl_138708 : CNF.NClause := [(38,false),(89,false),(144,false),(147,false),(129,false),(95,false),(104,false),(71,false),(86,false),(111,false)]
theorem der_138708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138708 :=
  CNF.rup_sound cl_138708 [cl_107682,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107682 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_138709 : CNF.NClause := [(117,true),(132,true),(76,false),(144,true),(21,false),(136,false),(71,false),(1,false),(53,false),(140,true)]
theorem der_138709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138709 :=
  CNF.rup_sound cl_138709 [cl_107686,cl_49771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107686 v h) (hints_cons _ _ _ (der_49771 v h) (by intro d hd; cases hd)))
def cl_138710 : CNF.NClause := [(46,false),(109,false),(150,false),(123,false),(111,false),(108,false),(136,false),(141,true),(152,true),(64,false)]
theorem der_138710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138710 :=
  CNF.rup_sound cl_138710 [cl_107689,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107689 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_138711 : CNF.NClause := [(151,false),(138,false),(125,true),(141,true),(42,true),(137,true),(148,true),(134,true),(80,false),(136,true)]
theorem der_138711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138711 :=
  CNF.rup_sound cl_138711 [cl_100143,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100143 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_138714 : CNF.NClause := [(89,false),(152,true),(113,false),(121,false),(110,false),(137,false),(153,false),(39,false),(150,true),(80,false)]
theorem der_138714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138714 :=
  CNF.rup_sound cl_138714 [cl_107699,cl_113157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107699 v h) (hints_cons _ _ _ (der_113157 v h) (by intro d hd; cases hd)))
def cl_138715 : CNF.NClause := [(45,false),(47,false),(136,false),(148,false),(63,false),(67,false),(64,false),(59,false),(95,false),(50,false)]
theorem der_138715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138715 :=
  CNF.rup_sound cl_138715 [cl_96348,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_96348 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138716 : CNF.NClause := [(126,false),(93,false),(85,false),(75,false),(99,false),(119,false),(64,false),(117,false),(60,false),(127,false)]
theorem der_138716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138716 :=
  CNF.rup_sound cl_138716 [cl_107700,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107700 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138717 : CNF.NClause := [(45,true),(140,false),(77,false),(84,false),(66,false),(38,true),(85,false),(68,false),(138,false),(76,false)]
theorem der_138717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138717 :=
  CNF.rup_sound cl_138717 [cl_104907,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104907 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138722 : CNF.NClause := [(131,false),(151,false),(101,false),(73,false),(106,false),(64,false),(96,false),(34,false),(82,false),(118,false)]
theorem der_138722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138722 :=
  CNF.rup_sound cl_138722 [cl_109474,cl_72318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109474 v h) (hints_cons _ _ _ (der_72318 v h) (by intro d hd; cases hd)))
def cl_138723 : CNF.NClause := [(35,false),(146,false),(126,false),(116,false),(153,false),(125,false),(53,false),(81,false),(73,false),(145,false)]
theorem der_138723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138723 :=
  CNF.rup_sound cl_138723 [cl_107704,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107704 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_138724 : CNF.NClause := [(89,false),(141,true),(29,false),(146,false),(143,true),(145,false),(84,false),(79,false),(71,false),(142,true)]
theorem der_138724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138724 :=
  CNF.rup_sound cl_138724 [cl_103467,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_103467 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_138727 : CNF.NClause := [(106,false),(99,false),(125,false),(84,false),(126,false),(44,false),(108,false),(131,true),(120,false),(47,false)]
theorem der_138727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138727 :=
  CNF.rup_sound cl_138727 [cl_107702,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107702 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_138728 : CNF.NClause := [(35,false),(134,false),(109,false),(128,false),(94,false),(118,false),(85,false),(129,false),(82,false),(99,false)]
theorem der_138728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138728 :=
  CNF.rup_sound cl_138728 [cl_110118,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110118 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138730 : CNF.NClause := [(35,false),(118,false),(141,false),(137,false),(104,false),(84,false),(94,false),(78,false),(99,false),(65,false)]
theorem der_138730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138730 :=
  CNF.rup_sound cl_138730 [cl_110202,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110202 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138731 : CNF.NClause := [(113,false),(38,false),(144,false),(72,false),(111,false),(71,false),(95,false),(73,false),(134,false),(120,false)]
theorem der_138731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138731 :=
  CNF.rup_sound cl_138731 [cl_114515,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114515 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_138732 : CNF.NClause := [(50,false),(108,false),(125,false),(127,false),(94,false),(75,false),(70,false),(121,false),(105,false),(65,false)]
theorem der_138732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138732 :=
  CNF.rup_sound cl_138732 [cl_116300,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116300 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138734 : CNF.NClause := [(55,true),(148,false),(152,true),(151,true),(143,true),(80,false),(134,true),(126,false),(147,true),(63,false)]
theorem der_138734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138734 :=
  CNF.rup_sound cl_138734 [cl_110514,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110514 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138735 : CNF.NClause := [(39,false),(148,false),(34,true),(151,true),(145,true),(126,false),(49,false),(129,true),(128,false),(143,false)]
theorem der_138735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138735 :=
  CNF.rup_sound cl_138735 [cl_116560,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116560 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_138737 : CNF.NClause := [(40,true),(133,false),(150,true),(131,true),(140,true),(143,false),(135,true),(144,true),(82,false),(130,true)]
theorem der_138737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138737 :=
  CNF.rup_sound cl_138737 [cl_116162,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116162 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_138738 : CNF.NClause := [(137,false),(89,false),(85,false),(140,true),(79,false),(141,true),(86,false),(29,false),(139,true),(142,true)]
theorem der_138738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138738 :=
  CNF.rup_sound cl_138738 [cl_115492,cl_66628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_115492 v h) (hints_cons _ _ _ (der_66628 v h) (by intro d hd; cases hd)))
def cl_138739 : CNF.NClause := [(100,false),(140,false),(66,false),(138,false),(42,false),(84,false),(111,false),(114,false),(121,false),(68,false)]
theorem der_138739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138739 :=
  CNF.rup_sound cl_138739 [cl_111355,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111355 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138740 : CNF.NClause := [(914,true),(905,true),(137,true),(912,false),(921,true),(65,false),(71,false),(44,true),(903,true),(72,false)]
theorem der_138740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138740 :=
  CNF.rup_sound cl_138740 [cl_111238,cl_112726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111238 v h) (hints_cons _ _ _ (der_112726 v h) (by intro d hd; cases hd)))
def cl_138742 : CNF.NClause := [(89,false),(143,true),(84,false),(142,true),(86,false),(71,false),(75,false),(141,true),(145,false),(9,false)]
theorem der_138742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138742 :=
  CNF.rup_sound cl_138742 [cl_113694,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113694 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_138743 : CNF.NClause := [(45,false),(117,false),(141,false),(133,false),(83,false),(110,false),(103,false),(70,false),(139,true),(120,false)]
theorem der_138743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138743 :=
  CNF.rup_sound cl_138743 [cl_113350,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113350 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_138744 : CNF.NClause := [(33,true),(141,true),(136,true),(84,false),(139,true),(153,true),(131,false),(135,true),(146,true),(148,true)]
theorem der_138744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138744 :=
  CNF.rup_sound cl_138744 [cl_116277,cl_88579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116277 v h) (hints_cons _ _ _ (der_88579 v h) (by intro d hd; cases hd)))
def cl_138745 : CNF.NClause := [(111,false),(49,false),(99,false),(150,false),(105,false),(65,false),(60,false),(73,false),(62,false),(119,false)]
theorem der_138745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138745 :=
  CNF.rup_sound cl_138745 [cl_110890,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110890 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_138746 : CNF.NClause := [(26,false),(36,false),(130,false),(51,false),(53,false),(62,false),(59,false),(83,false),(71,false),(39,false)]
theorem der_138746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138746 :=
  CNF.rup_sound cl_138746 [cl_113789,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113789 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138748 : CNF.NClause := [(95,false),(103,false),(43,false),(129,false),(144,false),(70,false),(67,false),(71,false),(122,false),(112,false)]
theorem der_138748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138748 :=
  CNF.rup_sound cl_138748 [cl_113956,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113956 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_138749 : CNF.NClause := [(108,true),(142,false),(126,true),(70,false),(83,false),(9,false),(76,false),(131,false),(50,false),(146,true)]
theorem der_138749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138749 :=
  CNF.rup_sound cl_138749 [cl_112960,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112960 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_138750 : CNF.NClause := [(45,false),(38,false),(23,false),(67,false),(39,false),(89,false),(125,false),(128,false),(74,false),(42,false)]
theorem der_138750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138750 :=
  CNF.rup_sound cl_138750 [cl_113409,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113409 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_138751 : CNF.NClause := [(45,false),(137,false),(71,false),(65,false),(153,false),(110,false),(120,false),(84,false),(94,false),(101,false)]
theorem der_138751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138751 :=
  CNF.rup_sound cl_138751 [cl_116709,cl_62596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_116709 v h) (hints_cons _ _ _ (der_62596 v h) (by intro d hd; cases hd)))
def cl_138753 : CNF.NClause := [(95,false),(130,false),(125,true),(140,true),(121,false),(91,false),(133,false),(53,false),(135,true),(117,false)]
theorem der_138753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138753 :=
  CNF.rup_sound cl_138753 [cl_120036,cl_57205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120036 v h) (hints_cons _ _ _ (der_57205 v h) (by intro d hd; cases hd)))
def cl_138754 : CNF.NClause := [(111,false),(131,true),(128,false),(60,false),(141,true),(119,false),(93,false),(136,true),(126,false),(90,false)]
theorem der_138754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138754 :=
  CNF.rup_sound cl_138754 [cl_110055,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110055 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138755 : CNF.NClause := [(113,false),(95,false),(38,false),(71,false),(150,false),(111,false),(83,false),(142,false),(120,false),(79,false)]
theorem der_138755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138755 :=
  CNF.rup_sound cl_138755 [cl_114914,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_114914 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138756 : CNF.NClause := [(94,false),(40,false),(144,false),(39,false),(75,false),(112,false),(72,false),(134,false),(70,false),(119,false)]
theorem der_138756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138756 :=
  CNF.rup_sound cl_138756 [cl_121534,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121534 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_138757 : CNF.NClause := [(136,false),(93,false),(120,false),(58,false),(100,false),(68,false),(81,false),(85,false),(130,false),(107,false)]
theorem der_138757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138757 :=
  CNF.rup_sound cl_138757 [cl_111501,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111501 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_138758 : CNF.NClause := [(26,false),(36,false),(83,false),(39,false),(71,false),(59,false),(41,false),(130,false),(62,false),(103,false)]
theorem der_138758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138758 :=
  CNF.rup_sound cl_138758 [cl_113858,cl_116001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113858 v h) (hints_cons _ _ _ (der_116001 v h) (by intro d hd; cases hd)))
def cl_138761 : CNF.NClause := [(147,false),(131,false),(55,false),(64,false),(84,false),(94,false),(79,false),(33,false),(125,false),(122,false)]
theorem der_138761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138761 :=
  CNF.rup_sound cl_138761 [cl_119185,cl_76537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119185 v h) (hints_cons _ _ _ (der_76537 v h) (by intro d hd; cases hd)))
def cl_138763 : CNF.NClause := [(125,false),(121,false),(73,false),(130,true),(133,false),(126,false),(140,true),(109,false),(135,true),(53,false)]
theorem der_138763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138763 :=
  CNF.rup_sound cl_138763 [cl_120298,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120298 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138769 : CNF.NClause := [(150,false),(146,false),(99,false),(137,false),(152,true),(113,false),(151,true),(107,false),(91,false),(39,false)]
theorem der_138769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138769 :=
  CNF.rup_sound cl_138769 [cl_120047,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120047 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_138770 : CNF.NClause := [(26,false),(27,false),(141,true),(143,true),(68,false),(131,false),(129,false),(142,true),(95,true),(79,false)]
theorem der_138770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138770 :=
  CNF.rup_sound cl_138770 [cl_122011,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_122011 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_138771 : CNF.NClause := [(16,false),(89,false),(133,false),(145,false),(84,false),(107,false),(39,false),(96,false),(75,false),(143,false)]
theorem der_138771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138771 :=
  CNF.rup_sound cl_138771 [cl_117395,cl_60437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117395 v h) (hints_cons _ _ _ (der_60437 v h) (by intro d hd; cases hd)))
def cl_138772 : CNF.NClause := [(54,false),(98,false),(141,false),(112,false),(74,false),(86,false),(60,false),(68,false),(120,false),(96,false)]
theorem der_138772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138772 :=
  CNF.rup_sound cl_138772 [cl_121191,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121191 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138773 : CNF.NClause := [(107,false),(133,false),(58,false),(137,false),(120,false),(68,false),(136,false),(152,true),(150,false),(89,false)]
theorem der_138773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138773 :=
  CNF.rup_sound cl_138773 [cl_120898,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120898 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_138774 : CNF.NClause := [(130,false),(44,false),(143,true),(133,true),(119,false),(96,false),(148,false),(128,true),(84,false),(131,false)]
theorem der_138774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138774 :=
  CNF.rup_sound cl_138774 [cl_120531,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120531 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138775 : CNF.NClause := [(47,false),(148,false),(120,false),(108,false),(99,false),(71,false),(150,false),(75,false),(97,false),(79,false)]
theorem der_138775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138775 :=
  CNF.rup_sound cl_138775 [cl_117228,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117228 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138778 : CNF.NClause := [(148,false),(150,false),(71,false),(48,false),(151,true),(83,false),(17,false),(50,false),(53,false),(39,false)]
theorem der_138778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138778 :=
  CNF.rup_sound cl_138778 [cl_119683,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119683 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138780 : CNF.NClause := [(140,false),(147,false),(113,false),(100,false),(40,false),(119,false),(94,false),(84,false),(77,false),(68,false)]
theorem der_138780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138780 :=
  CNF.rup_sound cl_138780 [cl_118735,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118735 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138781 : CNF.NClause := [(126,false),(103,false),(84,false),(96,false),(79,false),(69,false),(128,false),(44,false),(119,false),(102,false)]
theorem der_138781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138781 :=
  CNF.rup_sound cl_138781 [cl_117644,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117644 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_138782 : CNF.NClause := [(9,false),(40,false),(39,false),(143,false),(130,false),(134,true),(138,true),(64,false),(136,false),(48,false)]
theorem der_138782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138782 :=
  CNF.rup_sound cl_138782 [cl_118711,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118711 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_138783 : CNF.NClause := [(57,false),(102,false),(48,false),(71,false),(53,false),(148,false),(59,false),(83,false),(39,false),(75,false)]
theorem der_138783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138783 :=
  CNF.rup_sound cl_138783 [cl_119455,cl_79463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119455 v h) (hints_cons _ _ _ (der_79463 v h) (by intro d hd; cases hd)))
def cl_138788 : CNF.NClause := [(130,false),(142,false),(146,true),(148,false),(129,false),(147,true),(121,false),(50,false),(137,false),(108,false)]
theorem der_138788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138788 :=
  CNF.rup_sound cl_138788 [cl_117701,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117701 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138789 : CNF.NClause := [(94,false),(121,false),(144,false),(76,false),(134,false),(50,false),(74,false),(116,false),(73,false),(108,false)]
theorem der_138789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138789 :=
  CNF.rup_sound cl_138789 [cl_119072,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119072 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_138790 : CNF.NClause := [(142,false),(79,false),(113,false),(71,false),(94,false),(119,false),(40,false),(75,false),(150,false),(112,false)]
theorem der_138790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138790 :=
  CNF.rup_sound cl_138790 [cl_118504,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118504 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_138791 : CNF.NClause := [(130,false),(99,false),(150,false),(79,false),(47,false),(75,false),(120,false),(83,false),(108,false),(115,false)]
theorem der_138791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138791 :=
  CNF.rup_sound cl_138791 [cl_121143,cl_88593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121143 v h) (hints_cons _ _ _ (der_88593 v h) (by intro d hd; cases hd)))
def cl_138793 : CNF.NClause := [(47,false),(106,true),(18,false),(82,false),(134,true),(127,true),(140,false),(21,false),(146,true),(83,false)]
theorem der_138793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138793 :=
  CNF.rup_sound cl_138793 [cl_130376,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130376 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138795 : CNF.NClause := [(47,false),(142,false),(126,false),(63,false),(99,false),(97,false),(120,false),(106,false),(80,false),(148,false)]
theorem der_138795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138795 :=
  CNF.rup_sound cl_138795 [cl_130428,cl_80957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130428 v h) (hints_cons _ _ _ (der_80957 v h) (by intro d hd; cases hd)))
def cl_138797 : CNF.NClause := [(121,false),(127,false),(114,false),(141,true),(125,false),(100,false),(103,false),(42,false),(80,false),(85,false)]
theorem der_138797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138797 :=
  CNF.rup_sound cl_138797 [cl_124562,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124562 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_138798 : CNF.NClause := [(100,false),(140,false),(39,false),(126,false),(153,false),(60,false),(128,false),(48,false),(77,false),(150,true)]
theorem der_138798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138798 :=
  CNF.rup_sound cl_138798 [cl_126478,cl_88581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126478 v h) (hints_cons _ _ _ (der_88581 v h) (by intro d hd; cases hd)))
def cl_138799 : CNF.NClause := [(150,false),(151,false),(136,false),(64,false),(120,false),(53,false),(100,false),(83,false),(72,false),(39,false)]
theorem der_138799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138799 :=
  CNF.rup_sound cl_138799 [cl_124139,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124139 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138800 : CNF.NClause := [(100,false),(34,false),(75,false),(125,false),(85,false),(121,false),(114,false),(103,false),(42,false),(80,false)]
theorem der_138800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138800 :=
  CNF.rup_sound cl_138800 [cl_124534,cl_107195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124534 v h) (hints_cons _ _ _ (der_107195 v h) (by intro d hd; cases hd)))
def cl_138801 : CNF.NClause := [(40,true),(133,false),(138,true),(135,false),(151,true),(127,true),(134,true),(143,true),(129,true),(63,false)]
theorem der_138801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138801 :=
  CNF.rup_sound cl_138801 [cl_123890,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123890 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138802 : CNF.NClause := [(59,false),(99,false),(62,false),(111,false),(53,false),(37,false),(133,false),(80,false),(74,false),(60,false)]
theorem der_138802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138802 :=
  CNF.rup_sound cl_138802 [cl_129735,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_129735 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_138803 : CNF.NClause := [(142,false),(103,false),(133,true),(129,false),(44,false),(71,false),(132,true),(131,true),(144,false),(119,false)]
theorem der_138803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138803 :=
  CNF.rup_sound cl_138803 [cl_128137,cl_70134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128137 v h) (hints_cons _ _ _ (der_70134 v h) (by intro d hd; cases hd)))
def cl_138806 : CNF.NClause := [(33,false),(100,false),(140,false),(150,true),(145,false),(118,false),(153,false),(95,false),(77,false),(90,false)]
theorem der_138806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138806 :=
  CNF.rup_sound cl_138806 [cl_130195,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130195 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_138807 : CNF.NClause := [(16,false),(110,true),(126,false),(139,true),(73,false),(9,false),(83,false),(18,false),(132,true),(33,false)]
theorem der_138807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138807 :=
  CNF.rup_sound cl_138807 [cl_130188,cl_79662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130188 v h) (hints_cons _ _ _ (der_79662 v h) (by intro d hd; cases hd)))
def cl_138808 : CNF.NClause := [(152,true),(34,true),(141,true),(65,false),(138,true),(130,true),(1,false),(80,false),(85,false),(144,false)]
theorem der_138808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138808 :=
  CNF.rup_sound cl_138808 [cl_127127,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127127 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_138810 : CNF.NClause := [(33,false),(94,false),(19,false),(130,false),(150,false),(153,true),(53,false),(114,false),(50,false),(140,false)]
theorem der_138810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138810 :=
  CNF.rup_sound cl_138810 [cl_127484,cl_76724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127484 v h) (hints_cons _ _ _ (der_76724 v h) (by intro d hd; cases hd)))
def cl_138811 : CNF.NClause := [(133,false),(121,false),(114,false),(111,false),(145,false),(75,false),(103,false),(82,false),(42,false),(63,false)]
theorem der_138811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138811 :=
  CNF.rup_sound cl_138811 [cl_123922,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123922 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_138813 : CNF.NClause := [(148,false),(55,true),(153,true),(127,true),(141,true),(128,true),(151,false),(143,true),(138,true),(144,true)]
theorem der_138813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138813 :=
  CNF.rup_sound cl_138813 [cl_127178,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127178 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138815 : CNF.NClause := [(114,true),(135,false),(128,false),(150,true),(129,false),(136,true),(42,false),(138,true),(131,true),(143,true)]
theorem der_138815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138815 :=
  CNF.rup_sound cl_138815 [cl_124698,cl_137961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124698 v h) (hints_cons _ _ _ (der_137961 v h) (by intro d hd; cases hd)))
def cl_138816 : CNF.NClause := [(103,false),(129,false),(136,false),(144,false),(132,true),(112,false),(131,true),(43,false),(95,false),(133,true)]
theorem der_138816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138816 :=
  CNF.rup_sound cl_138816 [cl_126681,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126681 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_138818 : CNF.NClause := [(89,false),(142,true),(109,false),(96,false),(102,false),(140,false),(143,true),(44,false),(103,false),(139,true)]
theorem der_138818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138818 :=
  CNF.rup_sound cl_138818 [cl_128698,cl_79491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128698 v h) (hints_cons _ _ _ (der_79491 v h) (by intro d hd; cases hd)))
def cl_138819 : CNF.NClause := [(115,true),(10,false),(33,false),(133,true),(130,false),(140,false),(77,false),(83,false),(132,true),(139,true)]
theorem der_138819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138819 :=
  CNF.rup_sound cl_138819 [cl_130862,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130862 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_138821 : CNF.NClause := [(1066,false),(1056,true),(136,true),(142,true),(43,true),(130,true),(85,false),(24,false),(1071,true),(72,false)]
theorem der_138821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138821 :=
  CNF.rup_sound cl_138821 [cl_131414,cl_66240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131414 v h) (hints_cons _ _ _ (der_66240 v h) (by intro d hd; cases hd)))
def cl_138822 : CNF.NClause := [(142,true),(129,true),(111,false),(125,false),(146,true),(145,false),(138,true),(93,false),(50,false),(128,false)]
theorem der_138822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138822 :=
  CNF.rup_sound cl_138822 [cl_131431,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131431 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_138823 : CNF.NClause := [(129,false),(134,false),(18,false),(139,false),(138,true),(122,false),(49,false),(135,true),(136,true),(133,false)]
theorem der_138823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138823 :=
  CNF.rup_sound cl_138823 [cl_132151,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132151 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138826 : CNF.NClause := [(83,true),(914,true),(927,true),(915,true),(926,true),(918,true),(907,true),(913,true),(5,true),(900,true)]
theorem der_138826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138826 :=
  CNF.rup_sound cl_138826 [cl_132571,cl_137956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132571 v h) (hints_cons _ _ _ (der_137956 v h) (by intro d hd; cases hd)))
def cl_138827 : CNF.NClause := [(109,false),(41,false),(51,false),(80,false),(130,false),(148,false),(63,false),(76,false),(40,false),(52,false)]
theorem der_138827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138827 :=
  CNF.rup_sound cl_138827 [cl_132711,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132711 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_138828 : CNF.NClause := [(101,false),(59,false),(137,false),(121,false),(112,false),(138,true),(15,false),(135,true),(136,true),(153,false)]
theorem der_138828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138828 :=
  CNF.rup_sound cl_138828 [cl_133035,cl_88594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133035 v h) (hints_cons _ _ _ (der_88594 v h) (by intro d hd; cases hd)))
def cl_138830 : CNF.NClause := [(142,false),(60,false),(127,false),(143,true),(141,false),(148,true),(133,false),(136,false),(138,true),(77,false)]
theorem der_138830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138830 :=
  CNF.rup_sound cl_138830 [cl_133283,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133283 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138831 : CNF.NClause := [(109,false),(111,false),(46,false),(123,false),(141,false),(110,false),(77,false),(83,false),(70,false),(133,false)]
theorem der_138831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138831 :=
  CNF.rup_sound cl_138831 [cl_133289,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133289 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_138834 : CNF.NClause := [(122,false),(125,false),(34,false),(85,false),(5,false),(134,false),(128,false),(82,false),(84,false),(37,false)]
theorem der_138834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138834 :=
  CNF.rup_sound cl_138834 [cl_133596,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133596 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_138836 : CNF.NClause := [(115,false),(107,false),(128,false),(98,false),(122,false),(80,false),(55,false),(127,false),(75,false),(70,false)]
theorem der_138836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138836 :=
  CNF.rup_sound cl_138836 [cl_134344,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134344 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138837 : CNF.NClause := [(109,false),(142,false),(15,false),(110,false),(136,false),(111,false),(123,false),(77,false),(46,false),(64,false)]
theorem der_138837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138837 :=
  CNF.rup_sound cl_138837 [cl_134721,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134721 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_138838 : CNF.NClause := [(51,false),(126,false),(128,false),(139,false),(36,false),(55,false),(134,false),(84,false),(75,false),(64,false)]
theorem der_138838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138838 :=
  CNF.rup_sound cl_138838 [cl_134769,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134769 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_138840 : CNF.NClause := [(1058,false),(89,false),(1078,true),(86,false),(45,true),(1073,true),(72,false),(79,false),(1063,true),(70,false)]
theorem der_138840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138840 :=
  CNF.rup_sound cl_138840 [cl_135115,cl_107285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135115 v h) (hints_cons _ _ _ (der_107285 v h) (by intro d hd; cases hd)))
def cl_138842 : CNF.NClause := [(104,false),(148,false),(84,false),(52,false),(130,false),(110,false),(119,false),(116,false),(128,false),(67,false)]
theorem der_138842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138842 :=
  CNF.rup_sound cl_138842 [cl_135468,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135468 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138844 : CNF.NClause := [(40,false),(126,false),(136,false),(109,false),(127,false),(130,false),(80,false),(52,false),(69,false),(145,false)]
theorem der_138844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138844 :=
  CNF.rup_sound cl_138844 [cl_135727,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135727 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_138847 : CNF.NClause := [(142,false),(116,false),(143,false),(102,false),(121,false),(130,false),(138,true),(50,false),(128,true),(145,false)]
theorem der_138847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138847 :=
  CNF.rup_sound cl_138847 [cl_136521,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136521 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_138848 : CNF.NClause := [(102,false),(99,false),(51,false),(98,false),(126,false),(69,false),(123,false),(127,false),(79,false),(64,false)]
theorem der_138848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138848 :=
  CNF.rup_sound cl_138848 [cl_136678,cl_67569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136678 v h) (hints_cons _ _ _ (der_67569 v h) (by intro d hd; cases hd)))
def cl_138849 : CNF.NClause := [(111,false),(130,false),(110,false),(108,false),(123,false),(81,false),(136,false),(46,false),(85,false),(64,false)]
theorem der_138849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138849 :=
  CNF.rup_sound cl_138849 [cl_136811,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136811 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_138851 : CNF.NClause := [(48,false),(153,false),(130,false),(138,true),(133,true),(135,true),(152,false),(148,false),(128,true),(145,false)]
theorem der_138851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138851 :=
  CNF.rup_sound cl_138851 [cl_137047,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137047 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_138854 : CNF.NClause := [(94,false),(111,false),(129,false),(98,false),(55,false),(122,false),(86,false),(134,false),(82,false),(84,false)]
theorem der_138854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138854 :=
  CNF.rup_sound cl_138854 [cl_137124,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137124 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138855 : CNF.NClause := [(103,false),(129,false),(146,false),(43,false),(122,false),(71,false),(144,false),(59,false),(68,false),(67,false)]
theorem der_138855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138855 :=
  CNF.rup_sound cl_138855 [cl_137508,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137508 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_138856 : CNF.NClause := [(36,false),(39,false),(53,false),(46,false),(138,true),(148,false),(122,false),(128,true),(79,false),(21,false)]
theorem der_138856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138856 :=
  CNF.rup_sound cl_138856 [cl_137753,cl_107229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137753 v h) (hints_cons _ _ _ (der_107229 v h) (by intro d hd; cases hd)))
def cl_138857 : CNF.NClause := [(151,true),(131,true),(71,false),(80,false),(82,false),(7,false),(73,false),(140,true),(64,false),(120,true)]
theorem der_138857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138857 :=
  CNF.rup_sound cl_138857 [cl_137950,cl_138492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_137950 v h) (hints_cons _ _ _ (der_138492 v h) (by intro d hd; cases hd)))
def cl_138861 : CNF.NClause := [(108,false),(74,false),(50,false),(126,false),(102,false),(45,true),(84,false),(131,true),(128,false),(121,false),(116,false)]
theorem der_138861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138861 :=
  CNF.rup_sound cl_138861 [cl_107715,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107715 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_138862 : CNF.NClause := [(106,false),(125,false),(79,false),(119,false),(40,false),(94,false),(113,false),(84,false),(126,false),(131,true),(74,false)]
theorem der_138862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138862 :=
  CNF.rup_sound cl_138862 [cl_107719,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107719 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_138863 : CNF.NClause := [(109,false),(103,false),(127,false),(119,false),(80,false),(85,false),(44,false),(38,true),(125,false),(86,false),(115,false)]
theorem der_138863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138863 :=
  CNF.rup_sound cl_138863 [cl_107722,cl_79622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107722 v h) (hints_cons _ _ _ (der_79622 v h) (by intro d hd; cases hd)))
def cl_138866 : CNF.NClause := [(105,false),(48,true),(146,false),(41,false),(123,false),(104,false),(80,false),(39,true),(103,false),(127,false),(125,false)]
theorem der_138866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138866 :=
  CNF.rup_sound cl_138866 [cl_107726,cl_111314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107726 v h) (hints_cons _ _ _ (der_111314 v h) (by intro d hd; cases hd)))
def cl_138867 : CNF.NClause := [(89,false),(93,true),(88,false),(76,false),(75,false),(83,false),(152,false),(79,false),(91,false),(71,false),(59,false)]
theorem der_138867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138867 :=
  CNF.rup_sound cl_138867 [cl_81476,cl_87741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_81476 v h) (hints_cons _ _ _ (der_87741 v h) (by intro d hd; cases hd)))
def cl_138870 : CNF.NClause := [(109,false),(144,false),(138,true),(134,false),(70,false),(122,false),(113,false),(97,false),(75,false),(135,true),(37,false)]
theorem der_138870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138870 :=
  CNF.rup_sound cl_138870 [cl_107731,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107731 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_138875 : CNF.NClause := [(95,false),(109,false),(5,false),(85,false),(53,false),(98,false),(121,false),(134,false),(83,false),(84,false),(82,false)]
theorem der_138875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138875 :=
  CNF.rup_sound cl_138875 [cl_107740,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107740 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138876 : CNF.NClause := [(26,false),(130,false),(71,false),(79,false),(62,false),(98,false),(53,false),(121,false),(83,false),(95,false),(117,false)]
theorem der_138876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138876 :=
  CNF.rup_sound cl_138876 [cl_107742,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107742 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138877 : CNF.NClause := [(98,false),(95,false),(121,false),(53,false),(117,false),(65,false),(3,false),(80,false),(128,false),(85,false),(70,false)]
theorem der_138877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138877 :=
  CNF.rup_sound cl_138877 [cl_89263,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_89263 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138879 : CNF.NClause := [(26,false),(103,false),(123,false),(107,false),(79,false),(130,false),(71,false),(83,false),(104,false),(41,false),(62,false)]
theorem der_138879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138879 :=
  CNF.rup_sound cl_138879 [cl_107748,cl_116001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107748 v h) (hints_cons _ _ _ (der_116001 v h) (by intro d hd; cases hd)))
def cl_138881 : CNF.NClause := [(54,false),(4,false),(63,false),(37,false),(39,false),(83,false),(102,false),(125,false),(73,false),(49,false),(78,false)]
theorem der_138881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138881 :=
  CNF.rup_sound cl_138881 [cl_93755,cl_115972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93755 v h) (hints_cons _ _ _ (der_115972 v h) (by intro d hd; cases hd)))
def cl_138883 : CNF.NClause := [(150,false),(113,false),(84,false),(96,false),(128,false),(121,false),(39,false),(148,false),(71,false),(79,false),(99,false)]
theorem der_138883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138883 :=
  CNF.rup_sound cl_138883 [cl_107750,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107750 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138884 : CNF.NClause := [(38,false),(45,false),(59,false),(143,false),(144,false),(86,false),(72,false),(129,false),(80,false),(11,false),(66,false)]
theorem der_138884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138884 :=
  CNF.rup_sound cl_138884 [cl_107753,cl_107208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107753 v h) (hints_cons _ _ _ (der_107208 v h) (by intro d hd; cases hd)))
def cl_138885 : CNF.NClause := [(35,false),(38,false),(51,false),(130,false),(84,false),(24,false),(33,false),(67,false),(41,false),(80,false),(63,false)]
theorem der_138885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138885 :=
  CNF.rup_sound cl_138885 [cl_107756,cl_115964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107756 v h) (hints_cons _ _ _ (der_115964 v h) (by intro d hd; cases hd)))
def cl_138886 : CNF.NClause := [(1071,true),(1057,true),(1058,true),(1066,true),(1056,true),(63,true),(1083,true),(1074,true),(1060,true),(1064,true),(1069,true)]
theorem der_138886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138886 :=
  CNF.rup_sound cl_138886 [cl_106725,cl_137964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106725 v h) (hints_cons _ _ _ (der_137964 v h) (by intro d hd; cases hd)))
def cl_138887 : CNF.NClause := [(54,false),(47,false),(53,false),(45,false),(128,false),(85,false),(70,false),(80,false),(38,false),(3,false),(65,false)]
theorem der_138887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138887 :=
  CNF.rup_sound cl_138887 [cl_93143,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93143 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138888 : CNF.NClause := [(142,false),(12,false),(85,false),(113,false),(110,false),(39,false),(64,false),(15,false),(107,false),(72,false),(121,false)]
theorem der_138888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138888 :=
  CNF.rup_sound cl_138888 [cl_107763,cl_115972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107763 v h) (hints_cons _ _ _ (der_115972 v h) (by intro d hd; cases hd)))
def cl_138889 : CNF.NClause := [(39,false),(59,false),(143,false),(67,false),(117,false),(85,false),(129,false),(135,false),(70,false),(68,false),(20,false)]
theorem der_138889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138889 :=
  CNF.rup_sound cl_138889 [cl_107765,cl_107208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107765 v h) (hints_cons _ _ _ (der_107208 v h) (by intro d hd; cases hd)))
def cl_138890 : CNF.NClause := [(38,false),(58,false),(66,false),(143,false),(80,false),(45,false),(49,false),(37,false),(135,false),(71,false),(85,false)]
theorem der_138890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138890 :=
  CNF.rup_sound cl_138890 [cl_107767,cl_107208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107767 v h) (hints_cons _ _ _ (der_107208 v h) (by intro d hd; cases hd)))
def cl_138892 : CNF.NClause := [(133,true),(136,false),(126,false),(143,true),(39,false),(37,false),(42,false),(76,false),(128,false),(83,false),(138,true)]
theorem der_138892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138892 :=
  CNF.rup_sound cl_138892 [cl_107769,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107769 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138893 : CNF.NClause := [(151,true),(141,true),(144,true),(143,true),(49,true),(131,true),(134,true),(137,true),(69,false),(142,false),(132,false)]
theorem der_138893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138893 :=
  CNF.rup_sound cl_138893 [cl_107771,cl_86128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107771 v h) (hints_cons _ _ _ (der_86128 v h) (by intro d hd; cases hd)))
def cl_138895 : CNF.NClause := [(109,false),(142,false),(46,false),(110,false),(15,false),(64,false),(136,false),(111,false),(73,false),(123,false),(77,false)]
theorem der_138895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138895 :=
  CNF.rup_sound cl_138895 [cl_107776,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107776 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_138896 : CNF.NClause := [(121,false),(133,false),(117,false),(53,false),(75,false),(95,false),(82,false),(63,false),(137,false),(98,false),(78,false)]
theorem der_138896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138896 :=
  CNF.rup_sound cl_138896 [cl_100341,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100341 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_138897 : CNF.NClause := [(103,false),(105,false),(125,false),(127,false),(75,false),(123,false),(41,false),(104,false),(138,false),(80,false),(85,false)]
theorem der_138897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138897 :=
  CNF.rup_sound cl_138897 [cl_98357,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98357 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_138900 : CNF.NClause := [(112,false),(54,false),(105,false),(148,false),(138,false),(73,false),(114,false),(142,false),(77,false),(120,false),(84,false)]
theorem der_138900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138900 :=
  CNF.rup_sound cl_138900 [cl_107780,cl_115725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107780 v h) (hints_cons _ _ _ (der_115725 v h) (by intro d hd; cases hd)))
def cl_138903 : CNF.NClause := [(916,true),(914,false),(921,true),(904,true),(69,true),(925,true),(905,true),(922,true),(917,true),(919,true),(912,true)]
theorem der_138903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138903 :=
  CNF.rup_sound cl_138903 [cl_99379,cl_138004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99379 v h) (hints_cons _ _ _ (der_138004 v h) (by intro d hd; cases hd)))
def cl_138904 : CNF.NClause := [(36,false),(116,false),(141,false),(82,false),(77,false),(123,false),(133,false),(81,false),(117,false),(64,false),(115,false)]
theorem der_138904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138904 :=
  CNF.rup_sound cl_138904 [cl_102592,cl_119261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102592 v h) (hints_cons _ _ _ (der_119261 v h) (by intro d hd; cases hd)))
def cl_138906 : CNF.NClause := [(96,false),(129,false),(75,false),(34,false),(86,false),(134,false),(82,false),(128,false),(118,false),(111,false),(101,false)]
theorem der_138906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138906 :=
  CNF.rup_sound cl_138906 [cl_109806,cl_63986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_109806 v h) (hints_cons _ _ _ (der_63986 v h) (by intro d hd; cases hd)))
def cl_138907 : CNF.NClause := [(114,false),(133,false),(42,false),(121,false),(63,false),(111,false),(145,false),(75,false),(82,false),(103,false),(73,false)]
theorem der_138907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138907 :=
  CNF.rup_sound cl_138907 [cl_107786,cl_62196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107786 v h) (hints_cons _ _ _ (der_62196 v h) (by intro d hd; cases hd)))
def cl_138910 : CNF.NClause := [(117,false),(95,false),(74,false),(73,false),(53,false),(78,false),(121,false),(134,false),(98,false),(46,false),(75,false)]
theorem der_138910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138910 :=
  CNF.rup_sound cl_138910 [cl_102186,cl_107271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102186 v h) (hints_cons _ _ _ (der_107271 v h) (by intro d hd; cases hd)))
def cl_138911 : CNF.NClause := [(123,true),(73,false),(86,false),(85,false),(139,true),(75,false),(82,false),(74,false),(46,false),(84,false),(15,false)]
theorem der_138911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138911 :=
  CNF.rup_sound cl_138911 [cl_101747,cl_138039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101747 v h) (hints_cons _ _ _ (der_138039 v h) (by intro d hd; cases hd)))
def cl_138913 : CNF.NClause := [(117,true),(6,false),(142,false),(145,true),(131,true),(84,false),(83,false),(82,false),(128,true),(152,true),(129,false)]
theorem der_138913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138913 :=
  CNF.rup_sound cl_138913 [cl_112038,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112038 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_138916 : CNF.NClause := [(35,false),(141,false),(78,false),(137,false),(118,false),(104,false),(94,false),(84,false),(65,false),(72,false),(99,false)]
theorem der_138916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138916 :=
  CNF.rup_sound cl_138916 [cl_110130,cl_137957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110130 v h) (hints_cons _ _ _ (der_137957 v h) (by intro d hd; cases hd)))
def cl_138917 : CNF.NClause := [(45,false),(54,false),(136,false),(150,false),(71,false),(53,false),(116,false),(68,false),(152,true),(64,false),(39,false)]
theorem der_138917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138917 :=
  CNF.rup_sound cl_138917 [cl_112978,cl_62571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112978 v h) (hints_cons _ _ _ (der_62571 v h) (by intro d hd; cases hd)))
def cl_138918 : CNF.NClause := [(50,false),(140,false),(59,false),(82,false),(110,false),(5,false),(83,false),(84,false),(134,false),(85,false),(138,false)]
theorem der_138918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138918 :=
  CNF.rup_sound cl_138918 [cl_112324,cl_105698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112324 v h) (hints_cons _ _ _ (der_105698 v h) (by intro d hd; cases hd)))
def cl_138921 : CNF.NClause := [(52,true),(103,false),(42,false),(135,false),(143,true),(140,true),(125,true),(142,false),(114,false),(121,false),(139,true)]
theorem der_138921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138921 :=
  CNF.rup_sound cl_138921 [cl_113417,cl_128232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113417 v h) (hints_cons _ _ _ (der_128232 v h) (by intro d hd; cases hd)))
def cl_138922 : CNF.NClause := [(3,false),(105,true),(66,false),(146,true),(131,true),(82,false),(78,false),(74,false),(50,false),(6,false),(141,false)]
theorem der_138922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138922 :=
  CNF.rup_sound cl_138922 [cl_112085,cl_49827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112085 v h) (hints_cons _ _ _ (der_49827 v h) (by intro d hd; cases hd)))
def cl_138923 : CNF.NClause := [(89,false),(141,true),(71,false),(153,false),(125,true),(138,true),(145,false),(143,true),(146,true),(142,true),(86,false)]
theorem der_138923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138923 :=
  CNF.rup_sound cl_138923 [cl_115489,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_115489 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_138930 : CNF.NClause := [(117,false),(139,true),(121,false),(142,false),(143,true),(98,false),(140,true),(70,false),(53,false),(109,false),(133,false)]
theorem der_138930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138930 :=
  CNF.rup_sound cl_138930 [cl_113093,cl_102314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113093 v h) (hints_cons _ _ _ (der_102314 v h) (by intro d hd; cases hd)))
def cl_138931 : CNF.NClause := [(114,false),(133,false),(39,false),(103,false),(42,false),(73,false),(111,false),(67,false),(66,false),(85,false),(21,false)]
theorem der_138931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138931 :=
  CNF.rup_sound cl_138931 [cl_113334,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_113334 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_138932 : CNF.NClause := [(89,false),(142,true),(139,true),(148,true),(128,true),(137,false),(141,true),(140,true),(85,false),(138,false),(71,false)]
theorem der_138932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138932 :=
  CNF.rup_sound cl_138932 [cl_112019,cl_56745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112019 v h) (hints_cons _ _ _ (der_56745 v h) (by intro d hd; cases hd)))
def cl_138939 : CNF.NClause := [(3,false),(118,true),(65,false),(85,false),(70,false),(125,false),(86,false),(75,false),(71,false),(76,false),(80,false)]
theorem der_138939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138939 :=
  CNF.rup_sound cl_138939 [cl_123421,cl_56933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123421 v h) (hints_cons _ _ _ (der_56933 v h) (by intro d hd; cases hd)))
def cl_138940 : CNF.NClause := [(104,false),(10,false),(146,false),(143,false),(86,false),(73,false),(132,false),(36,false),(75,false),(42,false),(11,false)]
theorem der_138940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138940 :=
  CNF.rup_sound cl_138940 [cl_118304,cl_105763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_118304 v h) (hints_cons _ _ _ (der_105763 v h) (by intro d hd; cases hd)))
def cl_138941 : CNF.NClause := [(47,false),(101,false),(84,false),(121,false),(77,false),(65,false),(17,false),(147,false),(59,false),(93,false),(104,false)]
theorem der_138941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138941 :=
  CNF.rup_sound cl_138941 [cl_121312,cl_81199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121312 v h) (hints_cons _ _ _ (der_81199 v h) (by intro d hd; cases hd)))
def cl_138945 : CNF.NClause := [(34,true),(127,false),(131,true),(152,false),(85,false),(139,true),(133,true),(146,true),(147,true),(141,true),(80,false)]
theorem der_138945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138945 :=
  CNF.rup_sound cl_138945 [cl_117712,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_117712 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_138953 : CNF.NClause := [(38,false),(111,false),(134,false),(113,false),(75,false),(73,false),(71,false),(120,false),(68,false),(144,false),(95,false)]
theorem der_138953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138953 :=
  CNF.rup_sound cl_138953 [cl_121526,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121526 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_138954 : CNF.NClause := [(148,false),(39,false),(42,false),(86,false),(73,false),(50,false),(141,false),(18,false),(77,false),(85,false),(145,false)]
theorem der_138954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138954 :=
  CNF.rup_sound cl_138954 [cl_119332,cl_137960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119332 v h) (hints_cons _ _ _ (der_137960 v h) (by intro d hd; cases hd)))
def cl_138955 : CNF.NClause := [(109,false),(121,false),(77,false),(152,true),(140,false),(91,false),(53,false),(117,false),(147,false),(141,true),(136,false)]
theorem der_138955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138955 :=
  CNF.rup_sound cl_138955 [cl_120174,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120174 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_138956 : CNF.NClause := [(138,false),(131,false),(76,false),(80,false),(96,false),(130,false),(24,false),(67,false),(84,false),(119,false),(44,false)]
theorem der_138956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138956 :=
  CNF.rup_sound cl_138956 [cl_120551,cl_76534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_120551 v h) (hints_cons _ _ _ (der_76534 v h) (by intro d hd; cases hd)))
def cl_138958 : CNF.NClause := [(126,false),(130,false),(53,false),(136,false),(39,false),(85,false),(75,false),(42,false),(80,false),(69,false),(127,false)]
theorem der_138958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138958 :=
  CNF.rup_sound cl_138958 [cl_124923,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124923 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138959 : CNF.NClause := [(40,false),(128,false),(53,false),(39,false),(77,false),(70,false),(64,false),(17,false),(42,false),(83,false),(125,false)]
theorem der_138959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138959 :=
  CNF.rup_sound cl_138959 [cl_126143,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126143 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_138960 : CNF.NClause := [(121,false),(50,false),(150,true),(140,true),(137,false),(133,false),(102,false),(127,true),(129,false),(108,false),(146,true)]
theorem der_138960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138960 :=
  CNF.rup_sound cl_138960 [cl_127048,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127048 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_138962 : CNF.NClause := [(11,false),(35,false),(99,false),(94,false),(131,true),(136,true),(141,true),(114,false),(126,false),(4,false),(104,false)]
theorem der_138962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138962 :=
  CNF.rup_sound cl_138962 [cl_126931,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126931 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_138964 : CNF.NClause := [(121,false),(53,false),(70,false),(137,true),(95,false),(117,false),(142,true),(128,false),(140,false),(132,true),(127,false)]
theorem der_138964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138964 :=
  CNF.rup_sound cl_138964 [cl_130648,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130648 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_138967 : CNF.NClause := [(137,false),(45,false),(142,false),(129,true),(120,false),(63,false),(110,false),(133,false),(132,true),(131,true),(75,false)]
theorem der_138967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138967 :=
  CNF.rup_sound cl_138967 [cl_128208,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128208 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_138971 : CNF.NClause := [(110,false),(144,false),(45,false),(94,false),(129,false),(131,true),(120,false),(86,false),(83,false),(132,true),(103,false)]
theorem der_138971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138971 :=
  CNF.rup_sound cl_138971 [cl_128207,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_128207 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_138973 : CNF.NClause := [(34,true),(136,true),(127,false),(131,true),(60,true),(150,true),(143,false),(141,false),(137,true),(140,true),(132,true)]
theorem der_138973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138973 :=
  CNF.rup_sound cl_138973 [cl_127334,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127334 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_138975 : CNF.NClause := [(919,false),(73,true),(925,true),(917,true),(907,true),(909,true),(916,true),(914,true),(901,true),(905,true),(902,true)]
theorem der_138975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138975 :=
  CNF.rup_sound cl_138975 [cl_127976,cl_62084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127976 v h) (hints_cons _ _ _ (der_62084 v h) (by intro d hd; cases hd)))
def cl_138982 : CNF.NClause := [(128,false),(53,false),(84,false),(24,false),(67,false),(142,false),(125,false),(73,false),(42,false),(80,false),(39,false)]
theorem der_138982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138982 :=
  CNF.rup_sound cl_138982 [cl_125716,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125716 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_138983 : CNF.NClause := [(152,false),(153,true),(103,false),(123,false),(130,false),(41,false),(104,false),(151,true),(83,false),(107,false),(71,false)]
theorem der_138983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138983 :=
  CNF.rup_sound cl_138983 [cl_127377,cl_116001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127377 v h) (hints_cons _ _ _ (der_116001 v h) (by intro d hd; cases hd)))
def cl_138985 : CNF.NClause := [(97,false),(79,false),(144,false),(150,false),(119,false),(52,false),(104,false),(133,true),(132,true),(129,false),(131,true)]
theorem der_138985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138985 :=
  CNF.rup_sound cl_138985 [cl_127822,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127822 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138986 : CNF.NClause := [(137,true),(135,false),(74,false),(41,true),(76,false),(136,true),(143,true),(125,true),(131,true),(138,true),(150,false)]
theorem der_138986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138986 :=
  CNF.rup_sound cl_138986 [cl_124035,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124035 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_138988 : CNF.NClause := [(113,false),(126,false),(69,false),(122,false),(109,false),(127,false),(80,false),(85,false),(64,false),(97,false),(37,false)]
theorem der_138988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138988 :=
  CNF.rup_sound cl_138988 [cl_126001,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126001 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_138989 : CNF.NClause := [(127,true),(38,true),(100,false),(48,false),(151,false),(136,true),(143,true),(20,false),(59,false),(120,false),(44,false)]
theorem der_138989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138989 :=
  CNF.rup_sound cl_138989 [cl_127168,cl_79491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127168 v h) (hints_cons _ _ _ (der_79491 v h) (by intro d hd; cases hd)))
def cl_138993 : CNF.NClause := [(97,false),(110,false),(90,false),(104,false),(147,true),(52,false),(129,false),(119,false),(148,true),(145,false),(116,false)]
theorem der_138993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138993 :=
  CNF.rup_sound cl_138993 [cl_131178,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_131178 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_138994 : CNF.NClause := [(98,false),(111,false),(70,false),(152,false),(133,false),(122,false),(132,false),(55,false),(151,true),(81,false),(150,true)]
theorem der_138994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138994 :=
  CNF.rup_sound cl_138994 [cl_132079,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132079 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_138996 : CNF.NClause := [(111,true),(3,false),(75,false),(143,true),(133,false),(85,false),(70,false),(80,false),(18,false),(46,false),(138,true)]
theorem der_138996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138996 :=
  CNF.rup_sound cl_138996 [cl_132631,cl_49758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132631 v h) (hints_cons _ _ _ (der_49758 v h) (by intro d hd; cases hd)))
def cl_138998 : CNF.NClause := [(106,false),(41,false),(80,false),(67,false),(104,false),(63,false),(84,false),(24,false),(130,false),(103,false),(123,false)]
theorem der_138998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138998 :=
  CNF.rup_sound cl_138998 [cl_132778,cl_115964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_132778 v h) (hints_cons _ _ _ (der_115964 v h) (by intro d hd; cases hd)))
def cl_138999 : CNF.NClause := [(73,true),(904,true),(926,true),(901,true),(905,true),(922,true),(923,true),(919,true),(7,true),(914,false),(915,true)]
theorem der_138999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_138999 :=
  CNF.rup_sound cl_138999 [cl_133259,cl_120068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133259 v h) (hints_cons _ _ _ (der_120068 v h) (by intro d hd; cases hd)))
def cl_139002 : CNF.NClause := [(35,false),(33,false),(84,false),(142,false),(83,false),(134,false),(40,false),(136,false),(5,false),(82,false),(85,false)]
theorem der_139002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139002 :=
  CNF.rup_sound cl_139002 [cl_133548,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_133548 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_139004 : CNF.NClause := [(59,false),(5,false),(136,false),(82,false),(84,false),(142,false),(53,false),(83,false),(134,false),(86,false),(51,false)]
theorem der_139004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139004 :=
  CNF.rup_sound cl_139004 [cl_134327,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134327 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_139005 : CNF.NClause := [(152,false),(118,false),(132,false),(99,false),(128,false),(35,false),(114,false),(153,true),(130,false),(131,true),(135,true)]
theorem der_139005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139005 :=
  CNF.rup_sound cl_139005 [cl_134597,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_134597 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_139006 : CNF.NClause := [(142,false),(34,false),(33,false),(148,false),(76,false),(52,false),(84,false),(48,false),(63,false),(35,false),(67,false)]
theorem der_139006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139006 :=
  CNF.rup_sound cl_139006 [cl_135311,cl_115747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135311 v h) (hints_cons _ _ _ (der_115747 v h) (by intro d hd; cases hd)))
def cl_139007 : CNF.NClause := [(143,true),(153,true),(48,false),(123,false),(134,false),(40,false),(20,false),(52,false),(136,false),(126,true),(147,true)]
theorem der_139007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139007 :=
  CNF.rup_sound cl_139007 [cl_135702,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_135702 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_139009 : CNF.NClause := [(129,false),(77,false),(133,false),(86,false),(141,false),(82,false),(134,false),(49,false),(52,false),(55,false),(64,false)]
theorem der_139009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139009 :=
  CNF.rup_sound cl_139009 [cl_136021,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_136021 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_139017 : CNF.NClause := [(114,false),(113,false),(66,false),(41,false),(36,false),(116,false),(55,true),(117,false),(65,false),(84,false),(90,false),(59,false)]
theorem der_139017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139017 :=
  CNF.rup_sound cl_139017 [cl_80666,cl_115999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80666 v h) (hints_cons _ _ _ (der_115999 v h) (by intro d hd; cases hd)))
def cl_139018 : CNF.NClause := [(93,false),(60,false),(119,false),(141,true),(117,false),(139,false),(76,false),(72,false),(10,false),(99,false),(74,false),(73,false)]
theorem der_139018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139018 :=
  CNF.rup_sound cl_139018 [cl_107791,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107791 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_139024 : CNF.NClause := [(106,false),(40,false),(84,false),(2,false),(64,false),(74,false),(69,false),(94,false),(125,false),(119,false),(113,false),(79,false)]
theorem der_139024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139024 :=
  CNF.rup_sound cl_139024 [cl_107795,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107795 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_139025 : CNF.NClause := [(111,false),(2,false),(69,false),(125,false),(84,false),(74,false),(64,false),(94,false),(79,false),(98,false),(55,false),(122,false)]
theorem der_139025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139025 :=
  CNF.rup_sound cl_139025 [cl_107796,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107796 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_139027 : CNF.NClause := [(102,false),(2,false),(98,false),(84,false),(69,false),(123,false),(79,false),(74,false),(64,false),(51,false),(99,false),(127,false)]
theorem der_139027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139027 :=
  CNF.rup_sound cl_139027 [cl_107800,cl_127935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107800 v h) (hints_cons _ _ _ (der_127935 v h) (by intro d hd; cases hd)))
def cl_139028 : CNF.NClause := [(142,false),(115,false),(44,false),(12,false),(119,false),(102,false),(85,false),(72,false),(64,false),(68,false),(81,false),(109,false)]
theorem der_139028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139028 :=
  CNF.rup_sound cl_139028 [cl_107802,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107802 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_139029 : CNF.NClause := [(109,false),(58,false),(85,false),(93,false),(100,false),(134,false),(129,false),(84,false),(86,false),(120,false),(75,false),(82,false)]
theorem der_139029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139029 :=
  CNF.rup_sound cl_139029 [cl_86367,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_86367 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_139030 : CNF.NClause := [(39,false),(117,false),(59,false),(86,false),(2,false),(69,false),(125,false),(74,false),(64,false),(102,false),(42,false),(84,false)]
theorem der_139030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139030 :=
  CNF.rup_sound cl_139030 [cl_107804,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107804 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_139031 : CNF.NClause := [(113,false),(126,false),(69,false),(84,false),(127,false),(65,false),(85,false),(97,false),(109,false),(75,false),(37,false),(122,false)]
theorem der_139031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139031 :=
  CNF.rup_sound cl_139031 [cl_115222,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_115222 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_139032 : CNF.NClause := [(113,false),(111,false),(69,false),(64,false),(38,false),(2,false),(125,false),(120,false),(104,false),(74,false),(84,false),(79,false)]
theorem der_139032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139032 :=
  CNF.rup_sound cl_139032 [cl_107811,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107811 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_139034 : CNF.NClause := [(142,false),(45,false),(42,false),(19,false),(64,false),(152,false),(71,false),(63,false),(54,false),(85,false),(136,false),(74,false)]
theorem der_139034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139034 :=
  CNF.rup_sound cl_139034 [cl_107813,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107813 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_139035 : CNF.NClause := [(117,false),(72,false),(69,false),(11,false),(110,false),(66,false),(101,false),(120,false),(45,false),(83,false),(80,false),(143,false)]
theorem der_139035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139035 :=
  CNF.rup_sound cl_139035 [cl_107817,cl_107208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107817 v h) (hints_cons _ _ _ (der_107208 v h) (by intro d hd; cases hd)))
def cl_139038 : CNF.NClause := [(11,false),(115,false),(69,false),(117,false),(143,false),(80,false),(113,false),(72,false),(83,false),(66,false),(36,false),(123,false)]
theorem der_139038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139038 :=
  CNF.rup_sound cl_139038 [cl_107823,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107823 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_139043 : CNF.NClause := [(103,false),(117,false),(85,false),(101,false),(120,false),(133,false),(45,false),(131,true),(145,false),(129,true),(81,false),(73,false)]
theorem der_139043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139043 :=
  CNF.rup_sound cl_139043 [cl_100289,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_100289 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_139048 : CNF.NClause := [(114,false),(117,false),(126,false),(127,false),(85,false),(113,false),(36,false),(64,false),(123,false),(69,false),(75,false),(84,false)]
theorem der_139048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139048 :=
  CNF.rup_sound cl_139048 [cl_101426,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101426 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_139049 : CNF.NClause := [(151,false),(138,false),(152,true),(133,false),(82,false),(108,false),(89,false),(46,false),(123,false),(80,false),(150,true),(68,false)]
theorem der_139049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139049 :=
  CNF.rup_sound cl_139049 [cl_107840,cl_61644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107840 v h) (hints_cons _ _ _ (der_61644 v h) (by intro d hd; cases hd)))
def cl_139051 : CNF.NClause := [(114,false),(119,false),(101,false),(144,true),(146,false),(107,false),(48,false),(68,false),(140,false),(148,true),(90,false),(145,true)]
theorem der_139051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139051 :=
  CNF.rup_sound cl_139051 [cl_108610,cl_102901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108610 v h) (hints_cons _ _ _ (der_102901 v h) (by intro d hd; cases hd)))
def cl_139054 : CNF.NClause := [(83,false),(118,false),(138,false),(117,false),(32,false),(76,false),(77,false),(112,false),(64,false),(145,false),(102,false),(17,false)]
theorem der_139054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139054 :=
  CNF.rup_sound cl_139054 [cl_104162,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104162 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_139057 : CNF.NClause := [(114,false),(35,false),(67,false),(24,false),(99,false),(63,false),(142,false),(76,false),(109,false),(80,false),(84,false),(118,false)]
theorem der_139057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139057 :=
  CNF.rup_sound cl_139057 [cl_107846,cl_86128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107846 v h) (hints_cons _ _ _ (der_86128 v h) (by intro d hd; cases hd)))
def cl_139058 : CNF.NClause := [(45,false),(26,false),(53,false),(112,false),(62,false),(36,false),(79,false),(71,false),(83,false),(51,false),(136,false),(64,false)]
theorem der_139058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139058 :=
  CNF.rup_sound cl_139058 [cl_102038,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_102038 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_139059 : CNF.NClause := [(17,false),(103,false),(45,false),(138,false),(94,false),(83,false),(18,false),(76,false),(145,false),(117,false),(120,false),(64,false)]
theorem der_139059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139059 :=
  CNF.rup_sound cl_139059 [cl_104216,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104216 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_139063 : CNF.NClause := [(23,false),(14,false),(83,false),(81,false),(99,false),(39,false),(130,false),(110,false),(107,false),(121,false),(67,false),(12,false)]
theorem der_139063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139063 :=
  CNF.rup_sound cl_139063 [cl_110751,cl_137955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_110751 v h) (hints_cons _ _ _ (der_137955 v h) (by intro d hd; cases hd)))
def cl_139068 : CNF.NClause := [(135,false),(8,false),(75,false),(70,false),(102,false),(87,false),(32,false),(107,false),(3,false),(85,false),(112,false),(117,false)]
theorem der_139068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139068 :=
  CNF.rup_sound cl_139068 [cl_112612,cl_29848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_112612 v h) (hints_cons _ _ _ (der_29848 v h) (by intro d hd; cases hd)))
def cl_139076 : CNF.NClause := [(909,true),(901,true),(91,true),(902,true),(903,true),(6,false),(904,true),(917,true),(918,true),(906,true),(922,true),(926,true)]
theorem der_139076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139076 :=
  CNF.rup_sound cl_139076 [cl_111509,cl_107217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_111509 v h) (hints_cons _ _ _ (der_107217 v h) (by intro d hd; cases hd)))
def cl_139083 : CNF.NClause := [(152,true),(75,false),(151,true),(113,false),(137,false),(107,false),(71,false),(39,false),(121,false),(91,false),(153,false),(83,false)]
theorem der_139083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139083 :=
  CNF.rup_sound cl_139083 [cl_123543,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123543 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_139084 : CNF.NClause := [(3,false),(86,false),(148,false),(70,false),(53,false),(71,false),(63,false),(50,false),(85,false),(39,false),(130,false),(125,false)]
theorem der_139084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139084 :=
  CNF.rup_sound cl_139084 [cl_119971,cl_115963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119971 v h) (hints_cons _ _ _ (der_115963 v h) (by intro d hd; cases hd)))
def cl_139085 : CNF.NClause := [(4,false),(26,false),(143,false),(153,true),(138,true),(105,true),(152,true),(127,true),(141,false),(75,false),(50,false),(27,false)]
theorem der_139085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139085 :=
  CNF.rup_sound cl_139085 [cl_119768,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119768 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_139087 : CNF.NClause := [(114,false),(152,true),(142,true),(128,true),(29,false),(5,false),(113,false),(117,false),(115,false),(36,false),(131,true),(134,false)]
theorem der_139087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139087 :=
  CNF.rup_sound cl_139087 [cl_123413,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_123413 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_139099 : CNF.NClause := [(101,false),(59,false),(6,false),(153,false),(93,false),(145,false),(112,false),(63,false),(76,false),(121,false),(24,false),(84,false)]
theorem der_139099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139099 :=
  CNF.rup_sound cl_139099 [cl_121672,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_121672 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_139100 : CNF.NClause := [(94,true),(125,true),(129,true),(153,false),(27,false),(80,false),(67,false),(24,false),(50,false),(146,true),(84,false),(63,false)]
theorem der_139100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139100 :=
  CNF.rup_sound cl_139100 [cl_119287,cl_57423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_119287 v h) (hints_cons _ _ _ (der_57423 v h) (by intro d hd; cases hd)))
def cl_139106 : CNF.NClause := [(100,false),(18,false),(16,false),(114,false),(138,false),(84,false),(68,false),(111,false),(75,false),(42,false),(66,false),(121,false)]
theorem der_139106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139106 :=
  CNF.rup_sound cl_139106 [cl_125145,cl_138739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_125145 v h) (hints_cons _ _ _ (der_138739 v h) (by intro d hd; cases hd)))
def cl_139108 : CNF.NClause := [(121,false),(148,true),(53,false),(133,false),(141,false),(73,false),(144,true),(146,false),(128,true),(77,false),(151,false),(143,true)]
theorem der_139108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139108 :=
  CNF.rup_sound cl_139108 [cl_127338,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127338 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_139109 : CNF.NClause := [(4,false),(95,false),(43,false),(143,true),(68,false),(129,false),(150,true),(144,false),(122,false),(103,false),(131,true),(137,true)]
theorem der_139109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139109 :=
  CNF.rup_sound cl_139109 [cl_126773,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_126773 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_139116 : CNF.NClause := [(138,false),(131,false),(100,false),(129,false),(10,false),(72,false),(105,false),(118,false),(33,false),(86,false),(83,false),(79,false)]
theorem der_139116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139116 :=
  CNF.rup_sound cl_139116 [cl_130364,cl_57480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130364 v h) (hints_cons _ _ _ (der_57480 v h) (by intro d hd; cases hd)))
def cl_139117 : CNF.NClause := [(134,true),(125,false),(130,false),(143,true),(79,false),(153,true),(59,false),(150,false),(146,false),(42,false),(106,false),(147,true)]
theorem der_139117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139117 :=
  CNF.rup_sound cl_139117 [cl_124294,cl_61588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_124294 v h) (hints_cons _ _ _ (der_61588 v h) (by intro d hd; cases hd)))
def cl_139119 : CNF.NClause := [(34,true),(136,true),(127,false),(85,false),(131,true),(137,false),(132,true),(143,true),(150,true),(140,true),(80,false),(153,true)]
theorem der_139119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139119 :=
  CNF.rup_sound cl_139119 [cl_127161,cl_127935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127161 v h) (hints_cons _ _ _ (der_127935 v h) (by intro d hd; cases hd)))
def cl_139121 : CNF.NClause := [(110,false),(144,false),(120,false),(103,false),(84,false),(94,false),(45,false),(129,false),(83,false),(132,true),(85,false),(131,true)]
theorem der_139121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139121 :=
  CNF.rup_sound cl_139121 [cl_127689,cl_107242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_127689 v h) (hints_cons _ _ _ (der_107242 v h) (by intro d hd; cases hd)))
def cl_139122 : CNF.NClause := [(54,false),(114,false),(139,true),(105,false),(136,true),(145,false),(147,false),(120,false),(90,false),(141,false),(96,false),(126,false)]
theorem der_139122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_139122 :=
  CNF.rup_sound cl_139122 [cl_130517,cl_138294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_130517 v h) (hints_cons _ _ _ (der_138294 v h) (by intro d hd; cases hd)))
def chunk183 : List CNF.NClause := [cl_138320,cl_138321,cl_138322,cl_138323,cl_138324,cl_138325,cl_138327,cl_138328,cl_138331,cl_138332,cl_138333,cl_138334,cl_138335,cl_138336,cl_138337,cl_138338,cl_138339,cl_138340,cl_138341,cl_138343,cl_138344,cl_138346,cl_138347,cl_138348,cl_138349,cl_138350,cl_138351,cl_138352,cl_138353,cl_138355,cl_138356,cl_138357,cl_138358,cl_138359,cl_138360,cl_138361,cl_138362,cl_138363,cl_138364,cl_138365,cl_138366,cl_138367,cl_138368,cl_138369,cl_138370,cl_138371,cl_138374,cl_138375,cl_138376,cl_138377,cl_138378,cl_138379,cl_138380,cl_138381,cl_138383,cl_138385,cl_138387,cl_138389,cl_138392,cl_138394,cl_138395,cl_138396,cl_138397,cl_138398,cl_138399,cl_138400,cl_138401,cl_138402,cl_138403,cl_138404,cl_138405,cl_138407,cl_138410,cl_138411,cl_138412,cl_138414,cl_138416,cl_138417,cl_138418,cl_138419,cl_138420,cl_138422,cl_138424,cl_138425,cl_138427,cl_138429,cl_138430,cl_138431,cl_138432,cl_138435,cl_138436,cl_138437,cl_138439,cl_138440,cl_138441,cl_138442,cl_138444,cl_138445,cl_138446,cl_138447,cl_138448,cl_138451,cl_138452,cl_138453,cl_138454,cl_138455,cl_138456,cl_138457,cl_138458,cl_138460,cl_138461,cl_138462,cl_138463,cl_138464,cl_138465,cl_138466,cl_138468,cl_138469,cl_138470,cl_138471,cl_138472,cl_138473,cl_138474,cl_138475,cl_138477,cl_138478,cl_138479,cl_138480,cl_138481,cl_138482,cl_138483,cl_138484,cl_138485,cl_138486,cl_138487,cl_138488,cl_138489,cl_138490,cl_138491,cl_138492,cl_138495,cl_138497,cl_138501,cl_138502,cl_138503,cl_138504,cl_138505,cl_138507,cl_138508,cl_138509,cl_138510,cl_138512,cl_138513,cl_138514,cl_138516,cl_138517,cl_138518,cl_138519,cl_138520,cl_138521,cl_138522,cl_138523,cl_138524,cl_138525,cl_138526,cl_138527,cl_138528,cl_138529,cl_138530,cl_138531,cl_138532,cl_138533,cl_138534,cl_138535,cl_138536,cl_138537,cl_138539,cl_138540,cl_138542,cl_138543,cl_138544,cl_138545,cl_138546,cl_138547,cl_138548,cl_138549,cl_138550,cl_138551,cl_138552,cl_138553,cl_138554,cl_138555,cl_138558,cl_138559,cl_138560,cl_138562,cl_138563,cl_138564,cl_138565,cl_138566,cl_138568,cl_138571,cl_138574,cl_138575,cl_138576,cl_138579,cl_138580,cl_138581,cl_138582,cl_138584,cl_138585,cl_138586,cl_138589,cl_138590,cl_138593,cl_138595,cl_138596,cl_138597,cl_138599,cl_138600,cl_138601,cl_138602,cl_138604,cl_138605,cl_138608,cl_138610,cl_138612,cl_138613,cl_138617,cl_138619,cl_138620,cl_138621,cl_138623,cl_138625,cl_138626,cl_138627,cl_138628,cl_138631,cl_138632,cl_138633,cl_138634,cl_138636,cl_138638,cl_138639,cl_138641,cl_138642,cl_138643,cl_138644,cl_138645,cl_138648,cl_138650,cl_138651,cl_138652,cl_138653,cl_138654,cl_138657,cl_138658,cl_138659,cl_138660,cl_138663,cl_138664,cl_138665,cl_138666,cl_138667,cl_138668,cl_138670,cl_138671,cl_138674,cl_138675,cl_138676,cl_138677,cl_138678,cl_138679,cl_138680,cl_138681,cl_138682,cl_138690,cl_138691,cl_138692,cl_138694,cl_138696,cl_138697,cl_138699,cl_138700,cl_138701,cl_138702,cl_138703,cl_138705,cl_138706,cl_138707,cl_138708,cl_138709,cl_138710,cl_138711,cl_138714,cl_138715,cl_138716,cl_138717,cl_138722,cl_138723,cl_138724,cl_138727,cl_138728,cl_138730,cl_138731,cl_138732,cl_138734,cl_138735,cl_138737,cl_138738,cl_138739,cl_138740,cl_138742,cl_138743,cl_138744,cl_138745,cl_138746,cl_138748,cl_138749,cl_138750,cl_138751,cl_138753,cl_138754,cl_138755,cl_138756,cl_138757,cl_138758,cl_138761,cl_138763,cl_138769,cl_138770,cl_138771,cl_138772,cl_138773,cl_138774,cl_138775,cl_138778,cl_138780,cl_138781,cl_138782,cl_138783,cl_138788,cl_138789,cl_138790,cl_138791,cl_138793,cl_138795,cl_138797,cl_138798,cl_138799,cl_138800,cl_138801,cl_138802,cl_138803,cl_138806,cl_138807,cl_138808,cl_138810,cl_138811,cl_138813,cl_138815,cl_138816,cl_138818,cl_138819,cl_138821,cl_138822,cl_138823,cl_138826,cl_138827,cl_138828,cl_138830,cl_138831,cl_138834,cl_138836,cl_138837,cl_138838,cl_138840,cl_138842,cl_138844,cl_138847,cl_138848,cl_138849,cl_138851,cl_138854,cl_138855,cl_138856,cl_138857,cl_138861,cl_138862,cl_138863,cl_138866,cl_138867,cl_138870,cl_138875,cl_138876,cl_138877,cl_138879,cl_138881,cl_138883,cl_138884,cl_138885,cl_138886,cl_138887,cl_138888,cl_138889,cl_138890,cl_138892,cl_138893,cl_138895,cl_138896,cl_138897,cl_138900,cl_138903,cl_138904,cl_138906,cl_138907,cl_138910,cl_138911,cl_138913,cl_138916,cl_138917,cl_138918,cl_138921,cl_138922,cl_138923,cl_138930,cl_138931,cl_138932,cl_138939,cl_138940,cl_138941,cl_138945,cl_138953,cl_138954,cl_138955,cl_138956,cl_138958,cl_138959,cl_138960,cl_138962,cl_138964,cl_138967,cl_138971,cl_138973,cl_138975,cl_138982,cl_138983,cl_138985,cl_138986,cl_138988,cl_138989,cl_138993,cl_138994,cl_138996,cl_138998,cl_138999,cl_139002,cl_139004,cl_139005,cl_139006,cl_139007,cl_139009,cl_139017,cl_139018,cl_139024,cl_139025,cl_139027,cl_139028,cl_139029,cl_139030,cl_139031,cl_139032,cl_139034,cl_139035,cl_139038,cl_139043,cl_139048,cl_139049,cl_139051,cl_139054,cl_139057,cl_139058,cl_139059,cl_139063,cl_139068,cl_139076,cl_139083,cl_139084,cl_139085,cl_139087,cl_139099,cl_139100,cl_139106,cl_139108,cl_139109,cl_139116,cl_139117,cl_139119,cl_139121,cl_139122]
theorem chunk_sound183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk183, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_138320 v h) (hints_cons _ _ _ (der_138321 v h) (hints_cons _ _ _ (der_138322 v h) (hints_cons _ _ _ (der_138323 v h) (hints_cons _ _ _ (der_138324 v h) (hints_cons _ _ _ (der_138325 v h) (hints_cons _ _ _ (der_138327 v h) (hints_cons _ _ _ (der_138328 v h) (hints_cons _ _ _ (der_138331 v h) (hints_cons _ _ _ (der_138332 v h) (hints_cons _ _ _ (der_138333 v h) (hints_cons _ _ _ (der_138334 v h) (hints_cons _ _ _ (der_138335 v h) (hints_cons _ _ _ (der_138336 v h) (hints_cons _ _ _ (der_138337 v h) (hints_cons _ _ _ (der_138338 v h) (hints_cons _ _ _ (der_138339 v h) (hints_cons _ _ _ (der_138340 v h) (hints_cons _ _ _ (der_138341 v h) (hints_cons _ _ _ (der_138343 v h) (hints_cons _ _ _ (der_138344 v h) (hints_cons _ _ _ (der_138346 v h) (hints_cons _ _ _ (der_138347 v h) (hints_cons _ _ _ (der_138348 v h) (hints_cons _ _ _ (der_138349 v h) (hints_cons _ _ _ (der_138350 v h) (hints_cons _ _ _ (der_138351 v h) (hints_cons _ _ _ (der_138352 v h) (hints_cons _ _ _ (der_138353 v h) (hints_cons _ _ _ (der_138355 v h) (hints_cons _ _ _ (der_138356 v h) (hints_cons _ _ _ (der_138357 v h) (hints_cons _ _ _ (der_138358 v h) (hints_cons _ _ _ (der_138359 v h) (hints_cons _ _ _ (der_138360 v h) (hints_cons _ _ _ (der_138361 v h) (hints_cons _ _ _ (der_138362 v h) (hints_cons _ _ _ (der_138363 v h) (hints_cons _ _ _ (der_138364 v h) (hints_cons _ _ _ (der_138365 v h) (hints_cons _ _ _ (der_138366 v h) (hints_cons _ _ _ (der_138367 v h) (hints_cons _ _ _ (der_138368 v h) (hints_cons _ _ _ (der_138369 v h) (hints_cons _ _ _ (der_138370 v h) (hints_cons _ _ _ (der_138371 v h) (hints_cons _ _ _ (der_138374 v h) (hints_cons _ _ _ (der_138375 v h) (hints_cons _ _ _ (der_138376 v h) (hints_cons _ _ _ (der_138377 v h) (hints_cons _ _ _ (der_138378 v h) (hints_cons _ _ _ (der_138379 v h) (hints_cons _ _ _ (der_138380 v h) (hints_cons _ _ _ (der_138381 v h) (hints_cons _ _ _ (der_138383 v h) (hints_cons _ _ _ (der_138385 v h) (hints_cons _ _ _ (der_138387 v h) (hints_cons _ _ _ (der_138389 v h) (hints_cons _ _ _ (der_138392 v h) (hints_cons _ _ _ (der_138394 v h) (hints_cons _ _ _ (der_138395 v h) (hints_cons _ _ _ (der_138396 v h) (hints_cons _ _ _ (der_138397 v h) (hints_cons _ _ _ (der_138398 v h) (hints_cons _ _ _ (der_138399 v h) (hints_cons _ _ _ (der_138400 v h) (hints_cons _ _ _ (der_138401 v h) (hints_cons _ _ _ (der_138402 v h) (hints_cons _ _ _ (der_138403 v h) (hints_cons _ _ _ (der_138404 v h) (hints_cons _ _ _ (der_138405 v h) (hints_cons _ _ _ (der_138407 v h) (hints_cons _ _ _ (der_138410 v h) (hints_cons _ _ _ (der_138411 v h) (hints_cons _ _ _ (der_138412 v h) (hints_cons _ _ _ (der_138414 v h) (hints_cons _ _ _ (der_138416 v h) (hints_cons _ _ _ (der_138417 v h) (hints_cons _ _ _ (der_138418 v h) (hints_cons _ _ _ (der_138419 v h) (hints_cons _ _ _ (der_138420 v h) (hints_cons _ _ _ (der_138422 v h) (hints_cons _ _ _ (der_138424 v h) (hints_cons _ _ _ (der_138425 v h) (hints_cons _ _ _ (der_138427 v h) (hints_cons _ _ _ (der_138429 v h) (hints_cons _ _ _ (der_138430 v h) (hints_cons _ _ _ (der_138431 v h) (hints_cons _ _ _ (der_138432 v h) (hints_cons _ _ _ (der_138435 v h) (hints_cons _ _ _ (der_138436 v h) (hints_cons _ _ _ (der_138437 v h) (hints_cons _ _ _ (der_138439 v h) (hints_cons _ _ _ (der_138440 v h) (hints_cons _ _ _ (der_138441 v h) (hints_cons _ _ _ (der_138442 v h) (hints_cons _ _ _ (der_138444 v h) (hints_cons _ _ _ (der_138445 v h) (hints_cons _ _ _ (der_138446 v h) (hints_cons _ _ _ (der_138447 v h) (hints_cons _ _ _ (der_138448 v h) (hints_cons _ _ _ (der_138451 v h) (hints_cons _ _ _ (der_138452 v h) (hints_cons _ _ _ (der_138453 v h) (hints_cons _ _ _ (der_138454 v h) (hints_cons _ _ _ (der_138455 v h) (hints_cons _ _ _ (der_138456 v h) (hints_cons _ _ _ (der_138457 v h) (hints_cons _ _ _ (der_138458 v h) (hints_cons _ _ _ (der_138460 v h) (hints_cons _ _ _ (der_138461 v h) (hints_cons _ _ _ (der_138462 v h) (hints_cons _ _ _ (der_138463 v h) (hints_cons _ _ _ (der_138464 v h) (hints_cons _ _ _ (der_138465 v h) (hints_cons _ _ _ (der_138466 v h) (hints_cons _ _ _ (der_138468 v h) (hints_cons _ _ _ (der_138469 v h) (hints_cons _ _ _ (der_138470 v h) (hints_cons _ _ _ (der_138471 v h) (hints_cons _ _ _ (der_138472 v h) (hints_cons _ _ _ (der_138473 v h) (hints_cons _ _ _ (der_138474 v h) (hints_cons _ _ _ (der_138475 v h) (hints_cons _ _ _ (der_138477 v h) (hints_cons _ _ _ (der_138478 v h) (hints_cons _ _ _ (der_138479 v h) (hints_cons _ _ _ (der_138480 v h) (hints_cons _ _ _ (der_138481 v h) (hints_cons _ _ _ (der_138482 v h) (hints_cons _ _ _ (der_138483 v h) (hints_cons _ _ _ (der_138484 v h) (hints_cons _ _ _ (der_138485 v h) (hints_cons _ _ _ (der_138486 v h) (hints_cons _ _ _ (der_138487 v h) (hints_cons _ _ _ (der_138488 v h) (hints_cons _ _ _ (der_138489 v h) (hints_cons _ _ _ (der_138490 v h) (hints_cons _ _ _ (der_138491 v h) (hints_cons _ _ _ (der_138492 v h) (hints_cons _ _ _ (der_138495 v h) (hints_cons _ _ _ (der_138497 v h) (hints_cons _ _ _ (der_138501 v h) (hints_cons _ _ _ (der_138502 v h) (hints_cons _ _ _ (der_138503 v h) (hints_cons _ _ _ (der_138504 v h) (hints_cons _ _ _ (der_138505 v h) (hints_cons _ _ _ (der_138507 v h) (hints_cons _ _ _ (der_138508 v h) (hints_cons _ _ _ (der_138509 v h) (hints_cons _ _ _ (der_138510 v h) (hints_cons _ _ _ (der_138512 v h) (hints_cons _ _ _ (der_138513 v h) (hints_cons _ _ _ (der_138514 v h) (hints_cons _ _ _ (der_138516 v h) (hints_cons _ _ _ (der_138517 v h) (hints_cons _ _ _ (der_138518 v h) (hints_cons _ _ _ (der_138519 v h) (hints_cons _ _ _ (der_138520 v h) (hints_cons _ _ _ (der_138521 v h) (hints_cons _ _ _ (der_138522 v h) (hints_cons _ _ _ (der_138523 v h) (hints_cons _ _ _ (der_138524 v h) (hints_cons _ _ _ (der_138525 v h) (hints_cons _ _ _ (der_138526 v h) (hints_cons _ _ _ (der_138527 v h) (hints_cons _ _ _ (der_138528 v h) (hints_cons _ _ _ (der_138529 v h) (hints_cons _ _ _ (der_138530 v h) (hints_cons _ _ _ (der_138531 v h) (hints_cons _ _ _ (der_138532 v h) (hints_cons _ _ _ (der_138533 v h) (hints_cons _ _ _ (der_138534 v h) (hints_cons _ _ _ (der_138535 v h) (hints_cons _ _ _ (der_138536 v h) (hints_cons _ _ _ (der_138537 v h) (hints_cons _ _ _ (der_138539 v h) (hints_cons _ _ _ (der_138540 v h) (hints_cons _ _ _ (der_138542 v h) (hints_cons _ _ _ (der_138543 v h) (hints_cons _ _ _ (der_138544 v h) (hints_cons _ _ _ (der_138545 v h) (hints_cons _ _ _ (der_138546 v h) (hints_cons _ _ _ (der_138547 v h) (hints_cons _ _ _ (der_138548 v h) (hints_cons _ _ _ (der_138549 v h) (hints_cons _ _ _ (der_138550 v h) (hints_cons _ _ _ (der_138551 v h) (hints_cons _ _ _ (der_138552 v h) (hints_cons _ _ _ (der_138553 v h) (hints_cons _ _ _ (der_138554 v h) (hints_cons _ _ _ (der_138555 v h) (hints_cons _ _ _ (der_138558 v h) (hints_cons _ _ _ (der_138559 v h) (hints_cons _ _ _ (der_138560 v h) (hints_cons _ _ _ (der_138562 v h) (hints_cons _ _ _ (der_138563 v h) (hints_cons _ _ _ (der_138564 v h) (hints_cons _ _ _ (der_138565 v h) (hints_cons _ _ _ (der_138566 v h) (hints_cons _ _ _ (der_138568 v h) (hints_cons _ _ _ (der_138571 v h) (hints_cons _ _ _ (der_138574 v h) (hints_cons _ _ _ (der_138575 v h) (hints_cons _ _ _ (der_138576 v h) (hints_cons _ _ _ (der_138579 v h) (hints_cons _ _ _ (der_138580 v h) (hints_cons _ _ _ (der_138581 v h) (hints_cons _ _ _ (der_138582 v h) (hints_cons _ _ _ (der_138584 v h) (hints_cons _ _ _ (der_138585 v h) (hints_cons _ _ _ (der_138586 v h) (hints_cons _ _ _ (der_138589 v h) (hints_cons _ _ _ (der_138590 v h) (hints_cons _ _ _ (der_138593 v h) (hints_cons _ _ _ (der_138595 v h) (hints_cons _ _ _ (der_138596 v h) (hints_cons _ _ _ (der_138597 v h) (hints_cons _ _ _ (der_138599 v h) (hints_cons _ _ _ (der_138600 v h) (hints_cons _ _ _ (der_138601 v h) (hints_cons _ _ _ (der_138602 v h) (hints_cons _ _ _ (der_138604 v h) (hints_cons _ _ _ (der_138605 v h) (hints_cons _ _ _ (der_138608 v h) (hints_cons _ _ _ (der_138610 v h) (hints_cons _ _ _ (der_138612 v h) (hints_cons _ _ _ (der_138613 v h) (hints_cons _ _ _ (der_138617 v h) (hints_cons _ _ _ (der_138619 v h) (hints_cons _ _ _ (der_138620 v h) (hints_cons _ _ _ (der_138621 v h) (hints_cons _ _ _ (der_138623 v h) (hints_cons _ _ _ (der_138625 v h) (hints_cons _ _ _ (der_138626 v h) (hints_cons _ _ _ (der_138627 v h) (hints_cons _ _ _ (der_138628 v h) (hints_cons _ _ _ (der_138631 v h) (hints_cons _ _ _ (der_138632 v h) (hints_cons _ _ _ (der_138633 v h) (hints_cons _ _ _ (der_138634 v h) (hints_cons _ _ _ (der_138636 v h) (hints_cons _ _ _ (der_138638 v h) (hints_cons _ _ _ (der_138639 v h) (hints_cons _ _ _ (der_138641 v h) (hints_cons _ _ _ (der_138642 v h) (hints_cons _ _ _ (der_138643 v h) (hints_cons _ _ _ (der_138644 v h) (hints_cons _ _ _ (der_138645 v h) (hints_cons _ _ _ (der_138648 v h) (hints_cons _ _ _ (der_138650 v h) (hints_cons _ _ _ (der_138651 v h) (hints_cons _ _ _ (der_138652 v h) (hints_cons _ _ _ (der_138653 v h) (hints_cons _ _ _ (der_138654 v h) (hints_cons _ _ _ (der_138657 v h) (hints_cons _ _ _ (der_138658 v h) (hints_cons _ _ _ (der_138659 v h) (hints_cons _ _ _ (der_138660 v h) (hints_cons _ _ _ (der_138663 v h) (hints_cons _ _ _ (der_138664 v h) (hints_cons _ _ _ (der_138665 v h) (hints_cons _ _ _ (der_138666 v h) (hints_cons _ _ _ (der_138667 v h) (hints_cons _ _ _ (der_138668 v h) (hints_cons _ _ _ (der_138670 v h) (hints_cons _ _ _ (der_138671 v h) (hints_cons _ _ _ (der_138674 v h) (hints_cons _ _ _ (der_138675 v h) (hints_cons _ _ _ (der_138676 v h) (hints_cons _ _ _ (der_138677 v h) (hints_cons _ _ _ (der_138678 v h) (hints_cons _ _ _ (der_138679 v h) (hints_cons _ _ _ (der_138680 v h) (hints_cons _ _ _ (der_138681 v h) (hints_cons _ _ _ (der_138682 v h) (hints_cons _ _ _ (der_138690 v h) (hints_cons _ _ _ (der_138691 v h) (hints_cons _ _ _ (der_138692 v h) (hints_cons _ _ _ (der_138694 v h) (hints_cons _ _ _ (der_138696 v h) (hints_cons _ _ _ (der_138697 v h) (hints_cons _ _ _ (der_138699 v h) (hints_cons _ _ _ (der_138700 v h) (hints_cons _ _ _ (der_138701 v h) (hints_cons _ _ _ (der_138702 v h) (hints_cons _ _ _ (der_138703 v h) (hints_cons _ _ _ (der_138705 v h) (hints_cons _ _ _ (der_138706 v h) (hints_cons _ _ _ (der_138707 v h) (hints_cons _ _ _ (der_138708 v h) (hints_cons _ _ _ (der_138709 v h) (hints_cons _ _ _ (der_138710 v h) (hints_cons _ _ _ (der_138711 v h) (hints_cons _ _ _ (der_138714 v h) (hints_cons _ _ _ (der_138715 v h) (hints_cons _ _ _ (der_138716 v h) (hints_cons _ _ _ (der_138717 v h) (hints_cons _ _ _ (der_138722 v h) (hints_cons _ _ _ (der_138723 v h) (hints_cons _ _ _ (der_138724 v h) (hints_cons _ _ _ (der_138727 v h) (hints_cons _ _ _ (der_138728 v h) (hints_cons _ _ _ (der_138730 v h) (hints_cons _ _ _ (der_138731 v h) (hints_cons _ _ _ (der_138732 v h) (hints_cons _ _ _ (der_138734 v h) (hints_cons _ _ _ (der_138735 v h) (hints_cons _ _ _ (der_138737 v h) (hints_cons _ _ _ (der_138738 v h) (hints_cons _ _ _ (der_138739 v h) (hints_cons _ _ _ (der_138740 v h) (hints_cons _ _ _ (der_138742 v h) (hints_cons _ _ _ (der_138743 v h) (hints_cons _ _ _ (der_138744 v h) (hints_cons _ _ _ (der_138745 v h) (hints_cons _ _ _ (der_138746 v h) (hints_cons _ _ _ (der_138748 v h) (hints_cons _ _ _ (der_138749 v h) (hints_cons _ _ _ (der_138750 v h) (hints_cons _ _ _ (der_138751 v h) (hints_cons _ _ _ (der_138753 v h) (hints_cons _ _ _ (der_138754 v h) (hints_cons _ _ _ (der_138755 v h) (hints_cons _ _ _ (der_138756 v h) (hints_cons _ _ _ (der_138757 v h) (hints_cons _ _ _ (der_138758 v h) (hints_cons _ _ _ (der_138761 v h) (hints_cons _ _ _ (der_138763 v h) (hints_cons _ _ _ (der_138769 v h) (hints_cons _ _ _ (der_138770 v h) (hints_cons _ _ _ (der_138771 v h) (hints_cons _ _ _ (der_138772 v h) (hints_cons _ _ _ (der_138773 v h) (hints_cons _ _ _ (der_138774 v h) (hints_cons _ _ _ (der_138775 v h) (hints_cons _ _ _ (der_138778 v h) (hints_cons _ _ _ (der_138780 v h) (hints_cons _ _ _ (der_138781 v h) (hints_cons _ _ _ (der_138782 v h) (hints_cons _ _ _ (der_138783 v h) (hints_cons _ _ _ (der_138788 v h) (hints_cons _ _ _ (der_138789 v h) (hints_cons _ _ _ (der_138790 v h) (hints_cons _ _ _ (der_138791 v h) (hints_cons _ _ _ (der_138793 v h) (hints_cons _ _ _ (der_138795 v h) (hints_cons _ _ _ (der_138797 v h) (hints_cons _ _ _ (der_138798 v h) (hints_cons _ _ _ (der_138799 v h) (hints_cons _ _ _ (der_138800 v h) (hints_cons _ _ _ (der_138801 v h) (hints_cons _ _ _ (der_138802 v h) (hints_cons _ _ _ (der_138803 v h) (hints_cons _ _ _ (der_138806 v h) (hints_cons _ _ _ (der_138807 v h) (hints_cons _ _ _ (der_138808 v h) (hints_cons _ _ _ (der_138810 v h) (hints_cons _ _ _ (der_138811 v h) (hints_cons _ _ _ (der_138813 v h) (hints_cons _ _ _ (der_138815 v h) (hints_cons _ _ _ (der_138816 v h) (hints_cons _ _ _ (der_138818 v h) (hints_cons _ _ _ (der_138819 v h) (hints_cons _ _ _ (der_138821 v h) (hints_cons _ _ _ (der_138822 v h) (hints_cons _ _ _ (der_138823 v h) (hints_cons _ _ _ (der_138826 v h) (hints_cons _ _ _ (der_138827 v h) (hints_cons _ _ _ (der_138828 v h) (hints_cons _ _ _ (der_138830 v h) (hints_cons _ _ _ (der_138831 v h) (hints_cons _ _ _ (der_138834 v h) (hints_cons _ _ _ (der_138836 v h) (hints_cons _ _ _ (der_138837 v h) (hints_cons _ _ _ (der_138838 v h) (hints_cons _ _ _ (der_138840 v h) (hints_cons _ _ _ (der_138842 v h) (hints_cons _ _ _ (der_138844 v h) (hints_cons _ _ _ (der_138847 v h) (hints_cons _ _ _ (der_138848 v h) (hints_cons _ _ _ (der_138849 v h) (hints_cons _ _ _ (der_138851 v h) (hints_cons _ _ _ (der_138854 v h) (hints_cons _ _ _ (der_138855 v h) (hints_cons _ _ _ (der_138856 v h) (hints_cons _ _ _ (der_138857 v h) (hints_cons _ _ _ (der_138861 v h) (hints_cons _ _ _ (der_138862 v h) (hints_cons _ _ _ (der_138863 v h) (hints_cons _ _ _ (der_138866 v h) (hints_cons _ _ _ (der_138867 v h) (hints_cons _ _ _ (der_138870 v h) (hints_cons _ _ _ (der_138875 v h) (hints_cons _ _ _ (der_138876 v h) (hints_cons _ _ _ (der_138877 v h) (hints_cons _ _ _ (der_138879 v h) (hints_cons _ _ _ (der_138881 v h) (hints_cons _ _ _ (der_138883 v h) (hints_cons _ _ _ (der_138884 v h) (hints_cons _ _ _ (der_138885 v h) (hints_cons _ _ _ (der_138886 v h) (hints_cons _ _ _ (der_138887 v h) (hints_cons _ _ _ (der_138888 v h) (hints_cons _ _ _ (der_138889 v h) (hints_cons _ _ _ (der_138890 v h) (hints_cons _ _ _ (der_138892 v h) (hints_cons _ _ _ (der_138893 v h) (hints_cons _ _ _ (der_138895 v h) (hints_cons _ _ _ (der_138896 v h) (hints_cons _ _ _ (der_138897 v h) (hints_cons _ _ _ (der_138900 v h) (hints_cons _ _ _ (der_138903 v h) (hints_cons _ _ _ (der_138904 v h) (hints_cons _ _ _ (der_138906 v h) (hints_cons _ _ _ (der_138907 v h) (hints_cons _ _ _ (der_138910 v h) (hints_cons _ _ _ (der_138911 v h) (hints_cons _ _ _ (der_138913 v h) (hints_cons _ _ _ (der_138916 v h) (hints_cons _ _ _ (der_138917 v h) (hints_cons _ _ _ (der_138918 v h) (hints_cons _ _ _ (der_138921 v h) (hints_cons _ _ _ (der_138922 v h) (hints_cons _ _ _ (der_138923 v h) (hints_cons _ _ _ (der_138930 v h) (hints_cons _ _ _ (der_138931 v h) (hints_cons _ _ _ (der_138932 v h) (hints_cons _ _ _ (der_138939 v h) (hints_cons _ _ _ (der_138940 v h) (hints_cons _ _ _ (der_138941 v h) (hints_cons _ _ _ (der_138945 v h) (hints_cons _ _ _ (der_138953 v h) (hints_cons _ _ _ (der_138954 v h) (hints_cons _ _ _ (der_138955 v h) (hints_cons _ _ _ (der_138956 v h) (hints_cons _ _ _ (der_138958 v h) (hints_cons _ _ _ (der_138959 v h) (hints_cons _ _ _ (der_138960 v h) (hints_cons _ _ _ (der_138962 v h) (hints_cons _ _ _ (der_138964 v h) (hints_cons _ _ _ (der_138967 v h) (hints_cons _ _ _ (der_138971 v h) (hints_cons _ _ _ (der_138973 v h) (hints_cons _ _ _ (der_138975 v h) (hints_cons _ _ _ (der_138982 v h) (hints_cons _ _ _ (der_138983 v h) (hints_cons _ _ _ (der_138985 v h) (hints_cons _ _ _ (der_138986 v h) (hints_cons _ _ _ (der_138988 v h) (hints_cons _ _ _ (der_138989 v h) (hints_cons _ _ _ (der_138993 v h) (hints_cons _ _ _ (der_138994 v h) (hints_cons _ _ _ (der_138996 v h) (hints_cons _ _ _ (der_138998 v h) (hints_cons _ _ _ (der_138999 v h) (hints_cons _ _ _ (der_139002 v h) (hints_cons _ _ _ (der_139004 v h) (hints_cons _ _ _ (der_139005 v h) (hints_cons _ _ _ (der_139006 v h) (hints_cons _ _ _ (der_139007 v h) (hints_cons _ _ _ (der_139009 v h) (hints_cons _ _ _ (der_139017 v h) (hints_cons _ _ _ (der_139018 v h) (hints_cons _ _ _ (der_139024 v h) (hints_cons _ _ _ (der_139025 v h) (hints_cons _ _ _ (der_139027 v h) (hints_cons _ _ _ (der_139028 v h) (hints_cons _ _ _ (der_139029 v h) (hints_cons _ _ _ (der_139030 v h) (hints_cons _ _ _ (der_139031 v h) (hints_cons _ _ _ (der_139032 v h) (hints_cons _ _ _ (der_139034 v h) (hints_cons _ _ _ (der_139035 v h) (hints_cons _ _ _ (der_139038 v h) (hints_cons _ _ _ (der_139043 v h) (hints_cons _ _ _ (der_139048 v h) (hints_cons _ _ _ (der_139049 v h) (hints_cons _ _ _ (der_139051 v h) (hints_cons _ _ _ (der_139054 v h) (hints_cons _ _ _ (der_139057 v h) (hints_cons _ _ _ (der_139058 v h) (hints_cons _ _ _ (der_139059 v h) (hints_cons _ _ _ (der_139063 v h) (hints_cons _ _ _ (der_139068 v h) (hints_cons _ _ _ (der_139076 v h) (hints_cons _ _ _ (der_139083 v h) (hints_cons _ _ _ (der_139084 v h) (hints_cons _ _ _ (der_139085 v h) (hints_cons _ _ _ (der_139087 v h) (hints_cons _ _ _ (der_139099 v h) (hints_cons _ _ _ (der_139100 v h) (hints_cons _ _ _ (der_139106 v h) (hints_cons _ _ _ (der_139108 v h) (hints_cons _ _ _ (der_139109 v h) (hints_cons _ _ _ (der_139116 v h) (hints_cons _ _ _ (der_139117 v h) (hints_cons _ _ _ (der_139119 v h) (hints_cons _ _ _ (der_139121 v h) (hints_cons _ _ _ (der_139122 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix183 := prefix182 ++ chunk183
theorem prefix_sound183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix183, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound182 v h c hc
  · exact chunk_sound183 v h c hc
end Percolation.NReplay
