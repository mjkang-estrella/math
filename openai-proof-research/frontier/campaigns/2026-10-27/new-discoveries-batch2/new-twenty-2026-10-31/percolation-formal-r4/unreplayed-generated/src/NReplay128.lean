import NReplay127
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_107217 : CNF.NClause := [(911,false),(917,true),(91,true)]
theorem der_107217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107217 :=
  CNF.rup_sound cl_107217 [cl_15878,cl_76577,cl_15891,cl_76578,cl_15890,cl_37342,cl_15872,cl_15714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_76577 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_76578 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_37342 v h) (hints_cons _ _ _ (der_15872 v h) (hints_cons _ _ _ (der_15714 v h) (by intro d hd; cases hd)))))))))
def cl_107219 : CNF.NClause := [(909,false),(75,true)]
theorem der_107219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107219 :=
  CNF.rup_sound cl_107219 [cl_93635,cl_105705,cl_94890,cl_105788,cl_93640,cl_12699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_93635 v h) (hints_cons _ _ _ (der_105705 v h) (hints_cons _ _ _ (der_94890 v h) (hints_cons _ _ _ (der_105788 v h) (hints_cons _ _ _ (der_93640 v h) (hints_cons _ _ _ (inp_12699 v h) (by intro d hd; cases hd)))))))
def cl_107220 : CNF.NClause := [(246,false),(4,true),(3,true),(68,true)]
theorem der_107220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107220 :=
  CNF.rup_sound cl_107220 [cl_13884,cl_78573,cl_76590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13884 v h) (hints_cons _ _ _ (der_78573 v h) (hints_cons _ _ _ (der_76590 v h) (by intro d hd; cases hd))))
def cl_107221 : CNF.NClause := [(1074,false),(70,true)]
theorem der_107221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107221 :=
  CNF.rup_sound cl_107221 [cl_54843,cl_15926,cl_76580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54843 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (der_76580 v h) (by intro d hd; cases hd))))
def cl_107222 : CNF.NClause := [(129,false),(86,true)]
theorem der_107222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107222 :=
  CNF.rup_sound cl_107222 [cl_95938,cl_105791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_95938 v h) (hints_cons _ _ _ (der_105791 v h) (by intro d hd; cases hd)))
def cl_107223 : CNF.NClause := [(50,true),(90,false),(143,false)]
theorem der_107223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107223 :=
  CNF.rup_sound cl_107223 [cl_79625,cl_57470,cl_106183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79625 v h) (hints_cons _ _ _ (der_57470 v h) (hints_cons _ _ _ (der_106183 v h) (by intro d hd; cases hd))))
def cl_107224 : CNF.NClause := [(41,true),(92,false),(138,true),(134,false)]
theorem der_107224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107224 :=
  CNF.rup_sound cl_107224 [cl_98860,cl_72081,cl_106193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_98860 v h) (hints_cons _ _ _ (der_72081 v h) (hints_cons _ _ _ (der_106193 v h) (by intro d hd; cases hd))))
def cl_107226 : CNF.NClause := [(136,true),(148,true),(130,true),(151,true),(153,true),(73,true)]
theorem der_107226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107226 :=
  CNF.rup_sound cl_107226 [cl_88552,cl_15620,cl_86128,cl_15665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88552 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_86128 v h) (hints_cons _ _ _ (der_15665 v h) (by intro d hd; cases hd)))))
def cl_107227 : CNF.NClause := [(144,true),(134,true),(140,true),(142,true),(141,true),(85,true)]
theorem der_107227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107227 :=
  CNF.rup_sound cl_107227 [cl_57470,cl_15655,cl_63986,cl_15666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57470 v h) (hints_cons _ _ _ (der_15655 v h) (hints_cons _ _ _ (der_63986 v h) (hints_cons _ _ _ (der_15666 v h) (by intro d hd; cases hd)))))
def cl_107228 : CNF.NClause := [(1069,true),(1064,true),(1062,true),(1063,true),(1061,true),(70,true)]
theorem der_107228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107228 :=
  CNF.rup_sound cl_107228 [cl_54836,cl_15741,cl_107221,cl_15766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54836 v h) (hints_cons _ _ _ (der_15741 v h) (hints_cons _ _ _ (der_107221 v h) (hints_cons _ _ _ (der_15766 v h) (by intro d hd; cases hd)))))
def cl_107229 : CNF.NClause := [(53,false),(22,true)]
theorem der_107229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107229 :=
  CNF.rup_sound cl_107229 [cl_79506,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79506 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107230 : CNF.NClause := [(53,false),(78,true),(64,false)]
theorem der_107230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107230 :=
  CNF.rup_sound cl_107230 [cl_80150,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80150 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107231 : CNF.NClause := [(53,false),(75,true),(64,false)]
theorem der_107231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107231 :=
  CNF.rup_sound cl_107231 [cl_80151,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80151 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107232 : CNF.NClause := [(53,false),(64,true),(67,false)]
theorem der_107232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107232 :=
  CNF.rup_sound cl_107232 [cl_80175,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80175 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107233 : CNF.NClause := [(53,false),(67,false),(75,true)]
theorem der_107233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107233 :=
  CNF.rup_sound cl_107233 [cl_106054,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106054 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107234 : CNF.NClause := [(78,true),(53,false),(75,true)]
theorem der_107234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107234 :=
  CNF.rup_sound cl_107234 [cl_106055,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106055 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107235 : CNF.NClause := [(53,false),(78,true),(67,false)]
theorem der_107235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107235 :=
  CNF.rup_sound cl_107235 [cl_106058,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106058 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107236 : CNF.NClause := [(53,false),(78,true),(90,true)]
theorem der_107236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107236 :=
  CNF.rup_sound cl_107236 [cl_106059,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106059 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107239 : CNF.NClause := [(53,false),(75,false),(78,false),(64,true)]
theorem der_107239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107239 :=
  CNF.rup_sound cl_107239 [cl_80402,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80402 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107240 : CNF.NClause := [(53,false),(67,true),(75,false),(78,false),(90,false)]
theorem der_107240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107240 :=
  CNF.rup_sound cl_107240 [cl_52703,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52703 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107241 : CNF.NClause := [(75,true),(915,false)]
theorem der_107241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107241 :=
  CNF.rup_sound cl_107241 [cl_105788,cl_105705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105788 v h) (hints_cons _ _ _ (der_105705 v h) (by intro d hd; cases hd)))
def cl_107242 : CNF.NClause := [(86,true),(129,false)]
theorem der_107242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107242 :=
  CNF.rup_sound cl_107242 [cl_105791,cl_95938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105791 v h) (hints_cons _ _ _ (der_95938 v h) (by intro d hd; cases hd)))
def cl_107243 : CNF.NClause := [(81,true),(922,false)]
theorem der_107243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107243 :=
  CNF.rup_sound cl_107243 [cl_105811,cl_104421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105811 v h) (hints_cons _ _ _ (der_104421 v h) (by intro d hd; cases hd)))
def cl_107244 : CNF.NClause := [(88,true),(916,false)]
theorem der_107244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107244 :=
  CNF.rup_sound cl_107244 [cl_105812,cl_76539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105812 v h) (hints_cons _ _ _ (der_76539 v h) (by intro d hd; cases hd)))
def cl_107245 : CNF.NClause := [(90,true),(39,false),(76,false)]
theorem der_107245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107245 :=
  CNF.rup_sound cl_107245 [cl_105815,cl_79495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105815 v h) (hints_cons _ _ _ (der_79495 v h) (by intro d hd; cases hd)))
def cl_107246 : CNF.NClause := [(76,true),(68,false),(39,false)]
theorem der_107246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107246 :=
  CNF.rup_sound cl_107246 [cl_105816,cl_80917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105816 v h) (hints_cons _ _ _ (der_80917 v h) (by intro d hd; cases hd)))
def cl_107247 : CNF.NClause := [(36,false),(84,true),(83,false)]
theorem der_107247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107247 :=
  CNF.rup_sound cl_107247 [cl_105838,cl_107185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105838 v h) (hints_cons _ _ _ (der_107185 v h) (by intro d hd; cases hd)))
def cl_107248 : CNF.NClause := [(74,true),(54,false),(81,false)]
theorem der_107248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107248 :=
  CNF.rup_sound cl_107248 [cl_79796,cl_107186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79796 v h) (hints_cons _ _ _ (der_107186 v h) (by intro d hd; cases hd)))
def cl_107249 : CNF.NClause := [(67,true),(54,false),(83,false)]
theorem der_107249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107249 :=
  CNF.rup_sound cl_107249 [cl_105857,cl_107187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105857 v h) (hints_cons _ _ _ (der_107187 v h) (by intro d hd; cases hd)))
def cl_107250 : CNF.NClause := [(67,true),(65,false),(54,false)]
theorem der_107250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107250 :=
  CNF.rup_sound cl_107250 [cl_105861,cl_107249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105861 v h) (hints_cons _ _ _ (der_107249 v h) (by intro d hd; cases hd)))
def cl_107251 : CNF.NClause := [(62,true),(80,false),(60,false)]
theorem der_107251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107251 :=
  CNF.rup_sound cl_107251 [cl_79844,cl_105867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79844 v h) (hints_cons _ _ _ (der_105867 v h) (by intro d hd; cases hd)))
def cl_107252 : CNF.NClause := [(33,false),(84,true),(74,false)]
theorem der_107252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107252 :=
  CNF.rup_sound cl_107252 [cl_105969,cl_107182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105969 v h) (hints_cons _ _ _ (der_107182 v h) (by intro d hd; cases hd)))
def cl_107253 : CNF.NClause := [(79,true),(33,false),(84,false)]
theorem der_107253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107253 :=
  CNF.rup_sound cl_107253 [cl_79966,cl_107182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79966 v h) (hints_cons _ _ _ (der_107182 v h) (by intro d hd; cases hd)))
def cl_107254 : CNF.NClause := [(33,false),(64,true),(79,false)]
theorem der_107254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107254 :=
  CNF.rup_sound cl_107254 [cl_79971,cl_107182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79971 v h) (hints_cons _ _ _ (der_107182 v h) (by intro d hd; cases hd)))
def cl_107255 : CNF.NClause := [(74,true),(76,false),(41,false)]
theorem der_107255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107255 :=
  CNF.rup_sound cl_107255 [cl_105992,cl_107200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105992 v h) (hints_cons _ _ _ (der_107200 v h) (by intro d hd; cases hd)))
def cl_107256 : CNF.NClause := [(63,true),(35,false),(83,false)]
theorem der_107256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107256 :=
  CNF.rup_sound cl_107256 [cl_80037,cl_106006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80037 v h) (hints_cons _ _ _ (der_106006 v h) (by intro d hd; cases hd)))
def cl_107257 : CNF.NClause := [(35,false),(73,true),(63,true)]
theorem der_107257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107257 :=
  CNF.rup_sound cl_107257 [cl_106009,cl_107256] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106009 v h) (hints_cons _ _ _ (der_107256 v h) (by intro d hd; cases hd)))
def cl_107259 : CNF.NClause := [(90,true),(53,false),(67,false)]
theorem der_107259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107259 :=
  CNF.rup_sound cl_107259 [cl_106032,cl_107232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106032 v h) (hints_cons _ _ _ (der_107232 v h) (by intro d hd; cases hd)))
def cl_107260 : CNF.NClause := [(66,true),(52,false),(85,false)]
theorem der_107260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107260 :=
  CNF.rup_sound cl_107260 [cl_106048,cl_105773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106048 v h) (hints_cons _ _ _ (der_105773 v h) (by intro d hd; cases hd)))
def cl_107261 : CNF.NClause := [(85,false),(52,false),(73,true)]
theorem der_107261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107261 :=
  CNF.rup_sound cl_107261 [cl_80153,cl_105773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80153 v h) (hints_cons _ _ _ (der_105773 v h) (by intro d hd; cases hd)))
def cl_107262 : CNF.NClause := [(67,true),(85,false),(52,false)]
theorem der_107262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107262 :=
  CNF.rup_sound cl_107262 [cl_80154,cl_105773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80154 v h) (hints_cons _ _ _ (der_105773 v h) (by intro d hd; cases hd)))
def cl_107264 : CNF.NClause := [(52,false),(66,false),(88,true)]
theorem der_107264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107264 :=
  CNF.rup_sound cl_107264 [cl_80160,cl_105773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80160 v h) (hints_cons _ _ _ (der_105773 v h) (by intro d hd; cases hd)))
def cl_107266 : CNF.NClause := [(90,true),(64,false),(53,false)]
theorem der_107266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107266 :=
  CNF.rup_sound cl_107266 [cl_80163,cl_107236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80163 v h) (hints_cons _ _ _ (der_107236 v h) (by intro d hd; cases hd)))
def cl_107269 : CNF.NClause := [(53,false),(78,true),(67,false)]
theorem der_107269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107269 :=
  CNF.rup_sound cl_107269 [cl_80177,cl_107234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80177 v h) (hints_cons _ _ _ (der_107234 v h) (by intro d hd; cases hd)))
def cl_107270 : CNF.NClause := [(35,true),(87,false),(128,false)]
theorem der_107270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107270 :=
  CNF.rup_sound cl_107270 [cl_106062,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106062 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_107271 : CNF.NClause := [(79,true),(46,false),(78,false)]
theorem der_107271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107271 :=
  CNF.rup_sound cl_107271 [cl_106063,cl_107190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106063 v h) (hints_cons _ _ _ (der_107190 v h) (by intro d hd; cases hd)))
def cl_107272 : CNF.NClause := [(34,false),(70,false),(3,true)]
theorem der_107272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107272 :=
  CNF.rup_sound cl_107272 [cl_80206,cl_105766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80206 v h) (hints_cons _ _ _ (der_105766 v h) (by intro d hd; cases hd)))
def cl_107273 : CNF.NClause := [(132,false),(39,true),(90,false)]
theorem der_107273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107273 :=
  CNF.rup_sound cl_107273 [cl_106065,cl_79595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106065 v h) (hints_cons _ _ _ (der_79595 v h) (by intro d hd; cases hd)))
def cl_107275 : CNF.NClause := [(73,true),(21,false),(85,true)]
theorem der_107275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107275 :=
  CNF.rup_sound cl_107275 [cl_106071,cl_76964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106071 v h) (hints_cons _ _ _ (der_76964 v h) (by intro d hd; cases hd)))
def cl_107276 : CNF.NClause := [(152,false),(59,true),(90,false)]
theorem der_107276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107276 :=
  CNF.rup_sound cl_107276 [cl_106074,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106074 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107277 : CNF.NClause := [(139,false),(46,true),(92,false)]
theorem der_107277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107277 :=
  CNF.rup_sound cl_107277 [cl_106075,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106075 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_107278 : CNF.NClause := [(133,false),(17,false),(40,true)]
theorem der_107278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107278 :=
  CNF.rup_sound cl_107278 [cl_106078,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106078 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_107279 : CNF.NClause := [(146,false),(53,true),(19,false)]
theorem der_107279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107279 :=
  CNF.rup_sound cl_107279 [cl_106079,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106079 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107281 : CNF.NClause := [(151,false),(58,true),(16,false)]
theorem der_107281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107281 :=
  CNF.rup_sound cl_107281 [cl_106083,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106083 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_107282 : CNF.NClause := [(125,false),(4,false),(32,true)]
theorem der_107282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107282 :=
  CNF.rup_sound cl_107282 [cl_106084,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106084 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107283 : CNF.NClause := [(129,false),(20,false),(36,true)]
theorem der_107283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107283 :=
  CNF.rup_sound cl_107283 [cl_106085,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106085 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107284 : CNF.NClause := [(81,true),(9,false),(63,true)]
theorem der_107284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107284 :=
  CNF.rup_sound cl_107284 [cl_106086,cl_79648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106086 v h) (hints_cons _ _ _ (der_79648 v h) (by intro d hd; cases hd)))
def cl_107285 : CNF.NClause := [(138,false),(89,false),(45,true)]
theorem der_107285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107285 :=
  CNF.rup_sound cl_107285 [cl_106089,cl_76534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106089 v h) (hints_cons _ _ _ (der_76534 v h) (by intro d hd; cases hd)))
def cl_107286 : CNF.NClause := [(36,false),(5,true),(83,false)]
theorem der_107286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107286 :=
  CNF.rup_sound cl_107286 [cl_79513,cl_107185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79513 v h) (hints_cons _ _ _ (der_107185 v h) (by intro d hd; cases hd)))
def cl_107287 : CNF.NClause := [(146,false),(53,true),(8,false)]
theorem der_107287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107287 :=
  CNF.rup_sound cl_107287 [cl_106090,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106090 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107288 : CNF.NClause := [(130,false),(37,true),(91,false)]
theorem der_107288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107288 :=
  CNF.rup_sound cl_107288 [cl_106092,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106092 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107289 : CNF.NClause := [(146,false),(28,false),(53,true)]
theorem der_107289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107289 :=
  CNF.rup_sound cl_107289 [cl_106093,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106093 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107290 : CNF.NClause := [(139,false),(20,false),(46,true)]
theorem der_107290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107290 :=
  CNF.rup_sound cl_107290 [cl_106094,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106094 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_107291 : CNF.NClause := [(146,false),(11,false),(53,true)]
theorem der_107291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107291 :=
  CNF.rup_sound cl_107291 [cl_106095,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106095 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107292 : CNF.NClause := [(54,false),(67,false),(23,true)]
theorem der_107292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107292 :=
  CNF.rup_sound cl_107292 [cl_79584,cl_107187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79584 v h) (hints_cons _ _ _ (der_107187 v h) (by intro d hd; cases hd)))
def cl_107293 : CNF.NClause := [(15,true),(80,false),(46,false)]
theorem der_107293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107293 :=
  CNF.rup_sound cl_107293 [cl_79540,cl_107184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79540 v h) (hints_cons _ _ _ (der_107184 v h) (by intro d hd; cases hd)))
def cl_107294 : CNF.NClause := [(54,false),(67,true),(23,true)]
theorem der_107294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107294 :=
  CNF.rup_sound cl_107294 [cl_79582,cl_107250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79582 v h) (hints_cons _ _ _ (der_107250 v h) (by intro d hd; cases hd)))
def cl_107296 : CNF.NClause := [(135,false),(8,false),(42,true)]
theorem der_107296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107296 :=
  CNF.rup_sound cl_107296 [cl_106101,cl_86552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106101 v h) (hints_cons _ _ _ (der_86552 v h) (by intro d hd; cases hd)))
def cl_107297 : CNF.NClause := [(139,false),(46,true),(10,false)]
theorem der_107297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107297 :=
  CNF.rup_sound cl_107297 [cl_106102,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106102 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_107298 : CNF.NClause := [(139,false),(46,true),(5,false)]
theorem der_107298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107298 :=
  CNF.rup_sound cl_107298 [cl_106105,cl_63027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106105 v h) (hints_cons _ _ _ (der_63027 v h) (by intro d hd; cases hd)))
def cl_107299 : CNF.NClause := [(135,false),(28,false),(42,true)]
theorem der_107299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107299 :=
  CNF.rup_sound cl_107299 [cl_106106,cl_85856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106106 v h) (hints_cons _ _ _ (der_85856 v h) (by intro d hd; cases hd)))
def cl_107300 : CNF.NClause := [(125,false),(2,false),(32,true)]
theorem der_107300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107300 :=
  CNF.rup_sound cl_107300 [cl_106107,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106107 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107301 : CNF.NClause := [(79,true),(26,false),(75,true)]
theorem der_107301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107301 :=
  CNF.rup_sound cl_107301 [cl_106108,cl_76633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106108 v h) (hints_cons _ _ _ (der_76633 v h) (by intro d hd; cases hd)))
def cl_107302 : CNF.NClause := [(152,false),(59,true),(22,false)]
theorem der_107302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107302 :=
  CNF.rup_sound cl_107302 [cl_106110,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106110 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107303 : CNF.NClause := [(62,true),(83,true),(26,false)]
theorem der_107303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107303 :=
  CNF.rup_sound cl_107303 [cl_106111,cl_29836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106111 v h) (hints_cons _ _ _ (der_29836 v h) (by intro d hd; cases hd)))
def cl_107304 : CNF.NClause := [(900,false),(7,true),(71,true)]
theorem der_107304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107304 :=
  CNF.rup_sound cl_107304 [cl_106113,cl_96247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106113 v h) (hints_cons _ _ _ (der_96247 v h) (by intro d hd; cases hd)))
def cl_107305 : CNF.NClause := [(135,false),(22,false),(42,true)]
theorem der_107305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107305 :=
  CNF.rup_sound cl_107305 [cl_106117,cl_79623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106117 v h) (hints_cons _ _ _ (der_79623 v h) (by intro d hd; cases hd)))
def cl_107306 : CNF.NClause := [(129,false),(15,false),(36,true)]
theorem der_107306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107306 :=
  CNF.rup_sound cl_107306 [cl_106118,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106118 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107307 : CNF.NClause := [(1,false),(35,true),(128,false)]
theorem der_107307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107307 :=
  CNF.rup_sound cl_107307 [cl_106119,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106119 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_107308 : CNF.NClause := [(145,false),(17,false),(52,true)]
theorem der_107308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107308 :=
  CNF.rup_sound cl_107308 [cl_106120,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106120 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107309 : CNF.NClause := [(41,true),(15,false),(134,false)]
theorem der_107309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107309 :=
  CNF.rup_sound cl_107309 [cl_106121,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106121 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_107310 : CNF.NClause := [(150,false),(12,false),(57,true)]
theorem der_107310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107310 :=
  CNF.rup_sound cl_107310 [cl_106123,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106123 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_107311 : CNF.NClause := [(51,true),(144,false),(10,false)]
theorem der_107311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107311 :=
  CNF.rup_sound cl_107311 [cl_106127,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106127 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_107312 : CNF.NClause := [(37,false),(66,true),(78,false),(91,false)]
theorem der_107312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107312 :=
  CNF.rup_sound cl_107312 [cl_77620,cl_105818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77620 v h) (hints_cons _ _ _ (der_105818 v h) (by intro d hd; cases hd)))
def cl_107314 : CNF.NClause := [(37,false),(91,false),(70,true),(78,false)]
theorem der_107314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107314 :=
  CNF.rup_sound cl_107314 [cl_50639,cl_107312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50639 v h) (hints_cons _ _ _ (der_107312 v h) (by intro d hd; cases hd)))
def cl_107315 : CNF.NClause := [(37,false),(66,true),(70,false),(91,false)]
theorem der_107315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107315 :=
  CNF.rup_sound cl_107315 [cl_50642,cl_105820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50642 v h) (hints_cons _ _ _ (der_105820 v h) (by intro d hd; cases hd)))
def cl_107317 : CNF.NClause := [(37,false),(74,true),(70,false),(66,false)]
theorem der_107317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107317 :=
  CNF.rup_sound cl_107317 [cl_77633,cl_105822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77633 v h) (hints_cons _ _ _ (der_105822 v h) (by intro d hd; cases hd)))
def cl_107318 : CNF.NClause := [(37,false),(66,true),(74,false),(70,false)]
theorem der_107318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107318 :=
  CNF.rup_sound cl_107318 [cl_50652,cl_105823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50652 v h) (hints_cons _ _ _ (der_105823 v h) (by intro d hd; cases hd)))
def cl_107320 : CNF.NClause := [(86,false),(36,false),(82,false),(92,true)]
theorem der_107320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107320 :=
  CNF.rup_sound cl_107320 [cl_80253,cl_105835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80253 v h) (hints_cons _ _ _ (der_105835 v h) (by intro d hd; cases hd)))
def cl_107321 : CNF.NClause := [(58,false),(62,false),(69,false),(89,true)]
theorem der_107321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107321 :=
  CNF.rup_sound cl_107321 [cl_80265,cl_105848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80265 v h) (hints_cons _ _ _ (der_105848 v h) (by intro d hd; cases hd)))
def cl_107322 : CNF.NClause := [(58,false),(78,false),(89,true),(62,false)]
theorem der_107322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107322 :=
  CNF.rup_sound cl_107322 [cl_80268,cl_107321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80268 v h) (hints_cons _ _ _ (der_107321 v h) (by intro d hd; cases hd)))
def cl_107323 : CNF.NClause := [(65,false),(54,false),(74,true),(89,false)]
theorem der_107323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107323 :=
  CNF.rup_sound cl_107323 [cl_50778,cl_107250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50778 v h) (hints_cons _ _ _ (der_107250 v h) (by intro d hd; cases hd)))
def cl_107325 : CNF.NClause := [(74,true),(65,false),(83,false),(54,false)]
theorem der_107325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107325 :=
  CNF.rup_sound cl_107325 [cl_50786,cl_107250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50786 v h) (hints_cons _ _ _ (der_107250 v h) (by intro d hd; cases hd)))
def cl_107326 : CNF.NClause := [(54,false),(74,true),(67,false),(65,false)]
theorem der_107326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107326 :=
  CNF.rup_sound cl_107326 [cl_50805,cl_107292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50805 v h) (hints_cons _ _ _ (der_107292 v h) (by intro d hd; cases hd)))
def cl_107327 : CNF.NClause := [(88,false),(74,true),(80,false),(60,false)]
theorem der_107327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107327 :=
  CNF.rup_sound cl_107327 [cl_80279,cl_107251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80279 v h) (hints_cons _ _ _ (der_107251 v h) (by intro d hd; cases hd)))
def cl_107328 : CNF.NClause := [(60,false),(80,false),(86,true),(88,false)]
theorem der_107328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107328 :=
  CNF.rup_sound cl_107328 [cl_62170,cl_107327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62170 v h) (hints_cons _ _ _ (der_107327 v h) (by intro d hd; cases hd)))
def cl_107330 : CNF.NClause := [(86,false),(80,false),(29,true),(60,false)]
theorem der_107330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107330 :=
  CNF.rup_sound cl_107330 [cl_80285,cl_107251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80285 v h) (hints_cons _ _ _ (der_107251 v h) (by intro d hd; cases hd)))
def cl_107331 : CNF.NClause := [(80,false),(91,true),(84,false),(55,false)]
theorem der_107331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107331 :=
  CNF.rup_sound cl_107331 [cl_77882,cl_105881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77882 v h) (hints_cons _ _ _ (der_105881 v h) (by intro d hd; cases hd)))
def cl_107332 : CNF.NClause := [(79,false),(81,false),(46,false),(77,true)]
theorem der_107332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107332 :=
  CNF.rup_sound cl_107332 [cl_77914,cl_105906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77914 v h) (hints_cons _ _ _ (der_105906 v h) (by intro d hd; cases hd)))
def cl_107333 : CNF.NClause := [(79,true),(80,false),(77,false),(46,false)]
theorem der_107333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107333 :=
  CNF.rup_sound cl_107333 [cl_77921,cl_107293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77921 v h) (hints_cons _ _ _ (der_107293 v h) (by intro d hd; cases hd)))
def cl_107334 : CNF.NClause := [(92,true),(80,false),(46,false),(77,false)]
theorem der_107334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107334 :=
  CNF.rup_sound cl_107334 [cl_77939,cl_107293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77939 v h) (hints_cons _ _ _ (der_107293 v h) (by intro d hd; cases hd)))
def cl_107335 : CNF.NClause := [(46,false),(92,true),(15,true),(80,false)]
theorem der_107335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107335 :=
  CNF.rup_sound cl_107335 [cl_80322,cl_107334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80322 v h) (hints_cons _ _ _ (der_107334 v h) (by intro d hd; cases hd)))
def cl_107336 : CNF.NClause := [(42,false),(72,true),(80,false),(69,false)]
theorem der_107336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107336 :=
  CNF.rup_sound cl_107336 [cl_77949,cl_105921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77949 v h) (hints_cons _ _ _ (der_105921 v h) (by intro d hd; cases hd)))
def cl_107337 : CNF.NClause := [(42,false),(80,false),(66,true),(90,false)]
theorem der_107337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107337 :=
  CNF.rup_sound cl_107337 [cl_50931,cl_105924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50931 v h) (hints_cons _ _ _ (der_105924 v h) (by intro d hd; cases hd)))
def cl_107338 : CNF.NClause := [(42,false),(66,true),(69,false),(90,false)]
theorem der_107338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107338 :=
  CNF.rup_sound cl_107338 [cl_50935,cl_107337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50935 v h) (hints_cons _ _ _ (der_107337 v h) (by intro d hd; cases hd)))
def cl_107340 : CNF.NClause := [(42,false),(69,false),(83,true),(72,false)]
theorem der_107340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107340 :=
  CNF.rup_sound cl_107340 [cl_77981,cl_105925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_77981 v h) (hints_cons _ _ _ (der_105925 v h) (by intro d hd; cases hd)))
def cl_107341 : CNF.NClause := [(65,false),(75,true),(34,false),(3,false)]
theorem der_107341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107341 :=
  CNF.rup_sound cl_107341 [cl_80346,cl_106064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80346 v h) (hints_cons _ _ _ (der_106064 v h) (by intro d hd; cases hd)))
def cl_107342 : CNF.NClause := [(64,true),(83,false),(48,false),(70,false)]
theorem der_107342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107342 :=
  CNF.rup_sound cl_107342 [cl_80355,cl_107199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_80355 v h) (hints_cons _ _ _ (der_107199 v h) (by intro d hd; cases hd)))
def cl_107344 : CNF.NClause := [(81,true),(12,false),(43,false),(64,false)]
theorem der_107344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107344 :=
  CNF.rup_sound cl_107344 [cl_78086,cl_107205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78086 v h) (hints_cons _ _ _ (der_107205 v h) (by intro d hd; cases hd)))
def cl_107345 : CNF.NClause := [(79,true),(64,false),(33,false),(74,false)]
theorem der_107345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107345 :=
  CNF.rup_sound cl_107345 [cl_51121,cl_107182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51121 v h) (hints_cons _ _ _ (der_107182 v h) (by intro d hd; cases hd)))
def cl_107348 : CNF.NClause := [(92,true),(72,false),(76,false),(41,false)]
theorem der_107348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107348 :=
  CNF.rup_sound cl_107348 [cl_51231,cl_107255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51231 v h) (hints_cons _ _ _ (der_107255 v h) (by intro d hd; cases hd)))
def cl_107355 : CNF.NClause := [(49,false),(73,false),(91,true),(65,false)]
theorem der_107355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107355 :=
  CNF.rup_sound cl_107355 [cl_78487,cl_107181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78487 v h) (hints_cons _ _ _ (der_107181 v h) (by intro d hd; cases hd)))
def cl_107358 : CNF.NClause := [(75,true),(90,false),(53,false),(64,false)]
theorem der_107358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107358 :=
  CNF.rup_sound cl_107358 [cl_78497,cl_107229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_78497 v h) (hints_cons _ _ _ (der_107229 v h) (by intro d hd; cases hd)))
def cl_107360 : CNF.NClause := [(64,true),(53,false),(78,false),(90,false)]
theorem der_107360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107360 :=
  CNF.rup_sound cl_107360 [cl_51958,cl_107232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51958 v h) (hints_cons _ _ _ (der_107232 v h) (by intro d hd; cases hd)))
def cl_107361 : CNF.NClause := [(53,false),(75,false),(64,true),(90,false)]
theorem der_107361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107361 :=
  CNF.rup_sound cl_107361 [cl_51960,cl_107232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51960 v h) (hints_cons _ _ _ (der_107232 v h) (by intro d hd; cases hd)))
def cl_107365 : CNF.NClause := [(126,false),(1,false),(33,true),(131,true)]
theorem der_107365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107365 :=
  CNF.rup_sound cl_107365 [cl_106140,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106140 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_107366 : CNF.NClause := [(126,false),(33,true),(131,true),(3,false)]
theorem der_107366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107366 :=
  CNF.rup_sound cl_107366 [cl_106142,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106142 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107367 : CNF.NClause := [(126,false),(33,true),(131,true),(87,false)]
theorem der_107367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107367 :=
  CNF.rup_sound cl_107367 [cl_106143,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106143 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107369 : CNF.NClause := [(126,false),(33,true),(131,true),(4,false)]
theorem der_107369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107369 :=
  CNF.rup_sound cl_107369 [cl_106144,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106144 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107370 : CNF.NClause := [(145,false),(29,false),(135,true),(52,true)]
theorem der_107370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107370 :=
  CNF.rup_sound cl_107370 [cl_106154,cl_88561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106154 v h) (hints_cons _ _ _ (der_88561 v h) (by intro d hd; cases hd)))
def cl_107371 : CNF.NClause := [(145,false),(88,false),(135,true),(52,true)]
theorem der_107371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107371 :=
  CNF.rup_sound cl_107371 [cl_106155,cl_88561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106155 v h) (hints_cons _ _ _ (der_88561 v h) (by intro d hd; cases hd)))
def cl_107372 : CNF.NClause := [(150,false),(91,false),(152,true),(57,true)]
theorem der_107372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107372 :=
  CNF.rup_sound cl_107372 [cl_106156,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106156 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_107373 : CNF.NClause := [(148,false),(55,true),(26,false),(18,true)]
theorem der_107373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107373 :=
  CNF.rup_sound cl_107373 [cl_106158,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106158 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107374 : CNF.NClause := [(91,false),(43,true),(64,false),(136,false)]
theorem der_107374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107374 :=
  CNF.rup_sound cl_107374 [cl_106159,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106159 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107375 : CNF.NClause := [(145,false),(88,false),(73,false),(52,true)]
theorem der_107375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107375 :=
  CNF.rup_sound cl_107375 [cl_106162,cl_76522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106162 v h) (hints_cons _ _ _ (der_76522 v h) (by intro d hd; cases hd)))
def cl_107376 : CNF.NClause := [(43,true),(26,false),(68,false),(136,false)]
theorem der_107376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107376 :=
  CNF.rup_sound cl_107376 [cl_106164,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106164 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_107377 : CNF.NClause := [(145,false),(29,false),(73,false),(52,true)]
theorem der_107377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107377 :=
  CNF.rup_sound cl_107377 [cl_106166,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106166 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107378 : CNF.NClause := [(11,false),(50,true),(143,false),(77,false)]
theorem der_107378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107378 :=
  CNF.rup_sound cl_107378 [cl_106167,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106167 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_107379 : CNF.NClause := [(7,false),(80,true),(64,true),(12,true)]
theorem der_107379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107379 :=
  CNF.rup_sound cl_107379 [cl_106169,cl_49795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106169 v h) (hints_cons _ _ _ (der_49795 v h) (by intro d hd; cases hd)))
def cl_107380 : CNF.NClause := [(8,true),(16,true),(68,true),(1083,false)]
theorem der_107380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107380 :=
  CNF.rup_sound cl_107380 [cl_106172,cl_66240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106172 v h) (hints_cons _ _ _ (der_66240 v h) (by intro d hd; cases hd)))
def cl_107381 : CNF.NClause := [(150,false),(91,false),(28,false),(57,true)]
theorem der_107381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107381 :=
  CNF.rup_sound cl_107381 [cl_106177,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106177 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_107382 : CNF.NClause := [(133,false),(29,false),(63,false),(40,true)]
theorem der_107382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107382 :=
  CNF.rup_sound cl_107382 [cl_106178,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106178 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107383 : CNF.NClause := [(50,true),(143,false),(15,false),(22,false)]
theorem der_107383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107383 :=
  CNF.rup_sound cl_107383 [cl_106179,cl_79625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106179 v h) (hints_cons _ _ _ (der_79625 v h) (by intro d hd; cases hd)))
def cl_107384 : CNF.NClause := [(145,false),(17,false),(73,false),(52,true)]
theorem der_107384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107384 :=
  CNF.rup_sound cl_107384 [cl_106180,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106180 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107385 : CNF.NClause := [(150,false),(12,false),(83,false),(57,true)]
theorem der_107385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107385 :=
  CNF.rup_sound cl_107385 [cl_106181,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106181 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_107386 : CNF.NClause := [(126,false),(84,false),(33,true),(3,false)]
theorem der_107386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107386 :=
  CNF.rup_sound cl_107386 [cl_106186,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106186 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107387 : CNF.NClause := [(70,false),(29,false),(141,false),(48,true)]
theorem der_107387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107387 :=
  CNF.rup_sound cl_107387 [cl_106187,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106187 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_107388 : CNF.NClause := [(148,false),(18,false),(84,false),(55,true)]
theorem der_107388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107388 :=
  CNF.rup_sound cl_107388 [cl_106189,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106189 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107389 : CNF.NClause := [(43,true),(18,false),(81,false),(136,false)]
theorem der_107389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107389 :=
  CNF.rup_sound cl_107389 [cl_106190,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106190 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107390 : CNF.NClause := [(150,false),(18,false),(152,true),(57,true)]
theorem der_107390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107390 :=
  CNF.rup_sound cl_107390 [cl_106191,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106191 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_107391 : CNF.NClause := [(150,false),(152,true),(83,false),(6,false),(57,true)]
theorem der_107391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107391 :=
  CNF.rup_sound cl_107391 [cl_106195,cl_107385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106195 v h) (hints_cons _ _ _ (der_107385 v h) (by intro d hd; cases hd)))
def cl_107392 : CNF.NClause := [(133,false),(40,true),(88,false),(129,true),(131,true)]
theorem der_107392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107392 :=
  CNF.rup_sound cl_107392 [cl_106200,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106200 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_107393 : CNF.NClause := [(150,false),(91,false),(138,true),(57,true),(126,true)]
theorem der_107393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107393 :=
  CNF.rup_sound cl_107393 [cl_106206,cl_88593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106206 v h) (hints_cons _ _ _ (der_88593 v h) (by intro d hd; cases hd)))
def cl_107394 : CNF.NClause := [(41,true),(135,true),(138,true),(134,false),(20,false)]
theorem der_107394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107394 :=
  CNF.rup_sound cl_107394 [cl_106207,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106207 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_107395 : CNF.NClause := [(150,false),(24,false),(152,true),(71,false),(57,true)]
theorem der_107395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107395 :=
  CNF.rup_sound cl_107395 [cl_106210,cl_107390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106210 v h) (hints_cons _ _ _ (der_107390 v h) (by intro d hd; cases hd)))
def cl_107397 : CNF.NClause := [(88,false),(68,true),(74,false),(62,false),(60,false)]
theorem der_107397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107397 :=
  CNF.rup_sound cl_107397 [cl_106214,cl_77839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106214 v h) (hints_cons _ _ _ (der_77839 v h) (by intro d hd; cases hd)))
def cl_107398 : CNF.NClause := [(133,false),(88,false),(69,false),(63,false),(40,true)]
theorem der_107398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107398 :=
  CNF.rup_sound cl_107398 [cl_106217,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106217 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107399 : CNF.NClause := [(145,false),(88,false),(6,false),(67,false),(52,true)]
theorem der_107399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107399 :=
  CNF.rup_sound cl_107399 [cl_106218,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106218 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107400 : CNF.NClause := [(126,false),(84,false),(33,true),(64,false),(3,false)]
theorem der_107400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107400 :=
  CNF.rup_sound cl_107400 [cl_106219,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106219 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107403 : CNF.NClause := [(16,false),(75,true),(68,true),(12,true),(8,true)]
theorem der_107403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107403 :=
  CNF.rup_sound cl_107403 [cl_106223,cl_76590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106223 v h) (hints_cons _ _ _ (der_76590 v h) (by intro d hd; cases hd)))
def cl_107404 : CNF.NClause := [(126,false),(64,false),(33,true),(84,false),(4,false)]
theorem der_107404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107404 :=
  CNF.rup_sound cl_107404 [cl_106224,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106224 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107405 : CNF.NClause := [(126,false),(84,false),(33,true),(64,false),(87,false)]
theorem der_107405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107405 :=
  CNF.rup_sound cl_107405 [cl_106226,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106226 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107406 : CNF.NClause := [(150,false),(18,false),(71,false),(28,false),(57,true)]
theorem der_107406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107406 :=
  CNF.rup_sound cl_107406 [cl_106228,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106228 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_107407 : CNF.NClause := [(50,true),(28,false),(63,false),(143,false),(85,false)]
theorem der_107407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107407 :=
  CNF.rup_sound cl_107407 [cl_106229,cl_107208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106229 v h) (hints_cons _ _ _ (der_107208 v h) (by intro d hd; cases hd)))
def cl_107409 : CNF.NClause := [(17,false),(143,false),(22,false),(63,false),(50,true)]
theorem der_107409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107409 :=
  CNF.rup_sound cl_107409 [cl_106235,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106235 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_107410 : CNF.NClause := [(140,false),(14,false),(68,false),(75,false),(47,true)]
theorem der_107410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107410 :=
  CNF.rup_sound cl_107410 [cl_106236,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106236 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_107411 : CNF.NClause := [(138,false),(140,false),(84,false),(75,false),(120,true)]
theorem der_107411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107411 :=
  CNF.rup_sound cl_107411 [cl_106237,cl_56322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106237 v h) (hints_cons _ _ _ (der_56322 v h) (by intro d hd; cases hd)))
def cl_107412 : CNF.NClause := [(21,false),(70,false),(141,false),(77,false),(48,true)]
theorem der_107412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107412 :=
  CNF.rup_sound cl_107412 [cl_106238,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106238 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_107413 : CNF.NClause := [(18,false),(70,false),(141,false),(29,false),(48,true)]
theorem der_107413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107413 :=
  CNF.rup_sound cl_107413 [cl_106239,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106239 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_107414 : CNF.NClause := [(15,false),(70,false),(141,false),(29,false),(48,true)]
theorem der_107414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107414 :=
  CNF.rup_sound cl_107414 [cl_106241,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106241 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_107415 : CNF.NClause := [(133,false),(21,false),(63,false),(40,true),(82,false)]
theorem der_107415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107415 :=
  CNF.rup_sound cl_107415 [cl_106242,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106242 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107416 : CNF.NClause := [(21,false),(70,false),(141,false),(139,true),(48,true)]
theorem der_107416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107416 :=
  CNF.rup_sound cl_107416 [cl_106243,cl_102504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106243 v h) (hints_cons _ _ _ (der_102504 v h) (by intro d hd; cases hd)))
def cl_107417 : CNF.NClause := [(148,false),(18,false),(6,true),(22,true),(55,true),(145,true)]
theorem der_107417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107417 :=
  CNF.rup_sound cl_107417 [cl_106245,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106245 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107418 : CNF.NClause := [(148,false),(91,false),(63,false),(147,true),(22,true),(55,true)]
theorem der_107418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107418 :=
  CNF.rup_sound cl_107418 [cl_106246,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106246 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107419 : CNF.NClause := [(135,true),(143,true),(151,true),(150,true),(132,true),(86,true)]
theorem der_107419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107419 :=
  CNF.rup_sound cl_107419 [cl_59495,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59495 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107421 : CNF.NClause := [(137,false),(131,false),(135,true),(38,true),(134,true),(136,true)]
theorem der_107421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107421 :=
  CNF.rup_sound cl_107421 [cl_106262,cl_83907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106262 v h) (hints_cons _ _ _ (der_83907 v h) (by intro d hd; cases hd)))
def cl_107422 : CNF.NClause := [(147,false),(11,true),(89,false),(81,false),(54,true),(65,false)]
theorem der_107422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107422 :=
  CNF.rup_sound cl_107422 [cl_106263,cl_76537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106263 v h) (hints_cons _ _ _ (der_76537 v h) (by intro d hd; cases hd)))
def cl_107424 : CNF.NClause := [(151,false),(148,false),(88,false),(152,true),(38,false),(111,true)]
theorem der_107424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107424 :=
  CNF.rup_sound cl_107424 [cl_106265,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106265 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_107425 : CNF.NClause := [(77,true),(18,true),(68,true),(12,true),(4,true),(16,false)]
theorem der_107425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107425 :=
  CNF.rup_sound cl_107425 [cl_106266,cl_49826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106266 v h) (hints_cons _ _ _ (der_49826 v h) (by intro d hd; cases hd)))
def cl_107426 : CNF.NClause := [(76,true),(82,true),(8,false),(1,true),(10,true),(5,true)]
theorem der_107426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107426 :=
  CNF.rup_sound cl_107426 [cl_106269,cl_76626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106269 v h) (hints_cons _ _ _ (der_76626 v h) (by intro d hd; cases hd)))
def cl_107427 : CNF.NClause := [(151,false),(136,false),(88,false),(152,true),(51,false),(99,true)]
theorem der_107427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107427 :=
  CNF.rup_sound cl_107427 [cl_106271,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106271 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_107428 : CNF.NClause := [(910,true),(75,true),(903,true),(901,true),(905,true),(920,true)]
theorem der_107428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107428 :=
  CNF.rup_sound cl_107428 [cl_106273,cl_94890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106273 v h) (hints_cons _ _ _ (der_94890 v h) (by intro d hd; cases hd)))
def cl_107429 : CNF.NClause := [(69,true),(62,true),(27,false),(1080,true),(1083,true),(405,true)]
theorem der_107429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107429 :=
  CNF.rup_sound cl_107429 [cl_106275,cl_56890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106275 v h) (hints_cons _ _ _ (der_56890 v h) (by intro d hd; cases hd)))
def cl_107432 : CNF.NClause := [(72,true),(909,false),(76,false),(73,false),(74,false),(92,false)]
theorem der_107432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107432 :=
  CNF.rup_sound cl_107432 [cl_90300,cl_107219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90300 v h) (hints_cons _ _ _ (der_107219 v h) (by intro d hd; cases hd)))
def cl_107433 : CNF.NClause := [(76,true),(24,true),(8,false),(10,true),(68,true),(29,true)]
theorem der_107433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107433 :=
  CNF.rup_sound cl_107433 [cl_106281,cl_76625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106281 v h) (hints_cons _ _ _ (der_76625 v h) (by intro d hd; cases hd)))
def cl_107435 : CNF.NClause := [(908,false),(133,true),(18,true),(63,false),(40,true),(82,false)]
theorem der_107435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107435 :=
  CNF.rup_sound cl_107435 [cl_106288,cl_104421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106288 v h) (hints_cons _ _ _ (der_104421 v h) (by intro d hd; cases hd)))
def cl_107436 : CNF.NClause := [(131,false),(38,true),(71,false),(915,true),(82,false),(906,false)]
theorem der_107436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107436 :=
  CNF.rup_sound cl_107436 [cl_106291,cl_83907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106291 v h) (hints_cons _ _ _ (der_83907 v h) (by intro d hd; cases hd)))
def cl_107442 : CNF.NClause := [(43,true),(136,false),(131,true),(85,false),(141,true),(6,false),(10,false)]
theorem der_107442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107442 :=
  CNF.rup_sound cl_107442 [cl_106302,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106302 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_107445 : CNF.NClause := [(136,false),(150,false),(152,true),(71,false),(64,false),(72,false),(122,true)]
theorem der_107445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107445 :=
  CNF.rup_sound cl_107445 [cl_106315,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106315 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107446 : CNF.NClause := [(135,false),(132,false),(35,false),(104,false),(94,false),(118,false),(109,false)]
theorem der_107446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107446 :=
  CNF.rup_sound cl_107446 [cl_106317,cl_86552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106317 v h) (hints_cons _ _ _ (der_86552 v h) (by intro d hd; cases hd)))
def cl_107447 : CNF.NClause := [(146,false),(132,false),(41,false),(104,false),(123,false),(103,false),(105,false)]
theorem der_107447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107447 :=
  CNF.rup_sound cl_107447 [cl_106323,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106323 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107448 : CNF.NClause := [(152,false),(132,false),(58,false),(38,false),(52,false),(54,false),(60,false)]
theorem der_107448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107448 :=
  CNF.rup_sound cl_107448 [cl_106326,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106326 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107450 : CNF.NClause := [(135,false),(152,false),(46,false),(49,false),(45,false),(37,false),(36,false)]
theorem der_107450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107450 :=
  CNF.rup_sound cl_107450 [cl_106330,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106330 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107451 : CNF.NClause := [(135,false),(132,false),(46,false),(49,false),(55,false),(36,false),(51,false)]
theorem der_107451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107451 :=
  CNF.rup_sound cl_107451 [cl_106331,cl_86552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106331 v h) (hints_cons _ _ _ (der_86552 v h) (by intro d hd; cases hd)))
def cl_107455 : CNF.NClause := [(41,true),(909,false),(912,true),(92,false),(74,false),(76,false),(73,false),(913,true)]
theorem der_107455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107455 :=
  CNF.rup_sound cl_107455 [cl_52817,cl_107219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52817 v h) (hints_cons _ _ _ (der_107219 v h) (by intro d hd; cases hd)))
def cl_107456 : CNF.NClause := [(148,false),(55,true),(4,false),(6,false),(152,true),(5,true),(126,true),(13,true)]
theorem der_107456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107456 :=
  CNF.rup_sound cl_107456 [cl_106355,cl_80957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106355 v h) (hints_cons _ _ _ (der_80957 v h) (by intro d hd; cases hd)))
def cl_107458 : CNF.NClause := [(135,true),(86,true),(131,true),(141,true),(128,true),(134,true),(127,true),(137,true)]
theorem der_107458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107458 :=
  CNF.rup_sound cl_107458 [cl_106358,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106358 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107459 : CNF.NClause := [(126,false),(125,false),(7,true),(86,false),(84,false),(33,true),(143,true),(32,true)]
theorem der_107459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107459 :=
  CNF.rup_sound cl_107459 [cl_106362,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106362 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107460 : CNF.NClause := [(148,false),(62,false),(26,false),(83,false),(71,false),(75,false),(79,false),(122,true)]
theorem der_107460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107460 :=
  CNF.rup_sound cl_107460 [cl_106367,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106367 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107461 : CNF.NClause := [(125,false),(142,false),(88,false),(78,false),(132,true),(147,true),(38,false),(102,true)]
theorem der_107461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107461 :=
  CNF.rup_sound cl_107461 [cl_106370,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106370 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_107462 : CNF.NClause := [(130,false),(109,true),(131,true),(88,false),(143,true),(58,false),(125,true),(144,false)]
theorem der_107462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107462 :=
  CNF.rup_sound cl_107462 [cl_106375,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106375 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107463 : CNF.NClause := [(152,false),(132,false),(76,false),(44,false),(109,false),(119,false),(103,false),(102,false)]
theorem der_107463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107463 :=
  CNF.rup_sound cl_107463 [cl_106376,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106376 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107464 : CNF.NClause := [(132,false),(125,false),(89,false),(142,true),(67,false),(59,false),(137,true),(112,true)]
theorem der_107464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107464 :=
  CNF.rup_sound cl_107464 [cl_106381,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106381 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107466 : CNF.NClause := [(148,false),(136,false),(63,false),(33,false),(118,false),(110,false),(105,false),(100,false)]
theorem der_107466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107466 :=
  CNF.rup_sound cl_107466 [cl_106384,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106384 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_107467 : CNF.NClause := [(135,false),(129,false),(144,false),(42,false),(111,false),(121,false),(103,false),(97,false)]
theorem der_107467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107467 :=
  CNF.rup_sound cl_107467 [cl_106385,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106385 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107468 : CNF.NClause := [(126,false),(121,false),(131,true),(59,false),(93,false),(128,false),(112,false),(101,false)]
theorem der_107468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107468 :=
  CNF.rup_sound cl_107468 [cl_106386,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106386 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107469 : CNF.NClause := [(146,false),(152,false),(84,false),(40,false),(94,false),(113,false),(119,false),(100,false)]
theorem der_107469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107469 :=
  CNF.rup_sound cl_107469 [cl_106387,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106387 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107470 : CNF.NClause := [(130,false),(142,false),(86,false),(50,false),(94,false),(116,false),(121,false),(102,false)]
theorem der_107470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107470 :=
  CNF.rup_sound cl_107470 [cl_106388,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106388 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107471 : CNF.NClause := [(126,false),(112,false),(131,true),(43,false),(122,false),(116,false),(103,false),(128,false)]
theorem der_107471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107471 :=
  CNF.rup_sound cl_107471 [cl_106389,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106389 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107472 : CNF.NClause := [(146,false),(135,false),(83,false),(52,false),(104,false),(116,false),(119,false),(110,false)]
theorem der_107472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107472 :=
  CNF.rup_sound cl_107472 [cl_106390,cl_88559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106390 v h) (hints_cons _ _ _ (der_88559 v h) (by intro d hd; cases hd)))
def cl_107473 : CNF.NClause := [(146,false),(135,false),(83,false),(35,false),(104,false),(94,false),(118,false),(99,false)]
theorem der_107473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107473 :=
  CNF.rup_sound cl_107473 [cl_106391,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106391 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107475 : CNF.NClause := [(153,false),(145,false),(135,true),(46,false),(49,false),(58,false),(37,false),(51,false)]
theorem der_107475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107475 :=
  CNF.rup_sound cl_107475 [cl_106394,cl_88561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106394 v h) (hints_cons _ _ _ (der_88561 v h) (by intro d hd; cases hd)))
def cl_107476 : CNF.NClause := [(125,false),(128,false),(63,false),(49,false),(43,false),(58,false),(38,false),(37,false)]
theorem der_107476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107476 :=
  CNF.rup_sound cl_107476 [cl_106395,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106395 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107477 : CNF.NClause := [(151,false),(136,false),(88,false),(152,true),(68,false),(64,false),(35,false),(99,true)]
theorem der_107477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107477 :=
  CNF.rup_sound cl_107477 [cl_106396,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106396 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_107478 : CNF.NClause := [(135,false),(126,false),(128,false),(37,false),(122,false),(113,false),(101,false),(97,false)]
theorem der_107478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107478 :=
  CNF.rup_sound cl_107478 [cl_106397,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106397 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_107479 : CNF.NClause := [(138,false),(120,false),(125,false),(45,false),(128,false),(110,false),(103,false),(101,false)]
theorem der_107479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107479 :=
  CNF.rup_sound cl_107479 [cl_106398,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106398 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_107480 : CNF.NClause := [(126,false),(131,true),(128,false),(45,false),(120,false),(117,false),(103,false),(101,false)]
theorem der_107480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107480 :=
  CNF.rup_sound cl_107480 [cl_106399,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106399 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107481 : CNF.NClause := [(126,false),(125,false),(131,true),(41,false),(104,false),(123,false),(103,false),(106,false)]
theorem der_107481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107481 :=
  CNF.rup_sound cl_107481 [cl_106400,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106400 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107483 : CNF.NClause := [(144,false),(139,false),(71,false),(58,false),(120,false),(116,false),(93,false),(107,false)]
theorem der_107483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107483 :=
  CNF.rup_sound cl_107483 [cl_106403,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106403 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107484 : CNF.NClause := [(144,false),(139,false),(71,false),(55,false),(122,false),(94,false),(107,false),(115,false)]
theorem der_107484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107484 :=
  CNF.rup_sound cl_107484 [cl_106404,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106404 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107485 : CNF.NClause := [(909,true),(905,true),(915,true),(911,true),(88,true),(928,true),(900,true),(913,true)]
theorem der_107485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107485 :=
  CNF.rup_sound cl_107485 [cl_97426,cl_107244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_97426 v h) (hints_cons _ _ _ (der_107244 v h) (by intro d hd; cases hd)))
def cl_107486 : CNF.NClause := [(148,false),(136,false),(63,false),(46,false),(123,false),(109,false),(110,false),(108,false)]
theorem der_107486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107486 :=
  CNF.rup_sound cl_107486 [cl_106406,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106406 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))
def cl_107487 : CNF.NClause := [(126,false),(43,false),(128,false),(129,false),(71,false),(49,false),(144,false),(37,false)]
theorem der_107487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107487 :=
  CNF.rup_sound cl_107487 [cl_106407,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106407 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107489 : CNF.NClause := [(144,false),(139,false),(71,false),(34,false),(118,false),(116,false),(96,false),(106,false)]
theorem der_107489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107489 :=
  CNF.rup_sound cl_107489 [cl_106409,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106409 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107490 : CNF.NClause := [(144,false),(139,false),(71,false),(42,false),(121,false),(103,false),(114,false),(97,false)]
theorem der_107490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107490 :=
  CNF.rup_sound cl_107490 [cl_106410,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106410 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107491 : CNF.NClause := [(144,false),(139,false),(71,false),(49,false),(122,false),(104,false),(117,false),(96,false)]
theorem der_107491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107491 :=
  CNF.rup_sound cl_107491 [cl_106411,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106411 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107494 : CNF.NClause := [(138,false),(125,false),(128,false),(54,false),(120,false),(96,false),(105,false),(98,false)]
theorem der_107494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107494 :=
  CNF.rup_sound cl_107494 [cl_106414,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106414 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_107495 : CNF.NClause := [(126,false),(37,false),(131,true),(49,false),(43,false),(42,false),(128,false),(50,false)]
theorem der_107495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107495 :=
  CNF.rup_sound cl_107495 [cl_106415,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106415 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107496 : CNF.NClause := [(153,false),(145,false),(73,false),(46,false),(59,false),(42,false),(50,false),(51,false)]
theorem der_107496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107496 :=
  CNF.rup_sound cl_107496 [cl_106416,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106416 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107498 : CNF.NClause := [(146,false),(143,false),(15,false),(46,false),(123,false),(111,false),(110,false),(112,false)]
theorem der_107498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107498 :=
  CNF.rup_sound cl_107498 [cl_106423,cl_79625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106423 v h) (hints_cons _ _ _ (der_79625 v h) (by intro d hd; cases hd)))
def cl_107499 : CNF.NClause := [(146,false),(126,false),(125,false),(57,false),(122,false),(93,false),(114,false),(106,false)]
theorem der_107499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107499 :=
  CNF.rup_sound cl_107499 [cl_106428,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106428 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107500 : CNF.NClause := [(139,false),(129,false),(78,false),(39,false),(99,false),(121,false),(96,false),(107,false)]
theorem der_107500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107500 :=
  CNF.rup_sound cl_107500 [cl_106429,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106429 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107501 : CNF.NClause := [(137,false),(145,false),(128,false),(35,false),(94,false),(118,false),(99,false),(114,false)]
theorem der_107501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107501 :=
  CNF.rup_sound cl_107501 [cl_106430,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106430 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107502 : CNF.NClause := [(142,false),(150,false),(152,true),(35,false),(94,false),(118,false),(99,false),(109,false)]
theorem der_107502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107502 :=
  CNF.rup_sound cl_107502 [cl_106431,cl_71647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106431 v h) (hints_cons _ _ _ (der_71647 v h) (by intro d hd; cases hd)))
def cl_107504 : CNF.NClause := [(153,false),(137,false),(86,false),(59,false),(62,false),(104,false),(121,false),(112,false),(101,false)]
theorem der_107504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107504 :=
  CNF.rup_sound cl_107504 [cl_106440,cl_61980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106440 v h) (hints_cons _ _ _ (der_61980 v h) (by intro d hd; cases hd)))
def cl_107508 : CNF.NClause := [(138,false),(152,true),(134,false),(131,true),(141,true),(133,true),(132,true),(41,true),(127,true)]
theorem der_107508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107508 :=
  CNF.rup_sound cl_107508 [cl_106446,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106446 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_107510 : CNF.NClause := [(148,false),(18,true),(128,false),(152,true),(132,true),(140,true),(55,true),(151,true),(144,true)]
theorem der_107510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107510 :=
  CNF.rup_sound cl_107510 [cl_106448,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106448 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107511 : CNF.NClause := [(146,false),(133,true),(141,true),(142,true),(51,true),(143,true),(144,false),(150,true),(127,true)]
theorem der_107511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107511 :=
  CNF.rup_sound cl_107511 [cl_106451,cl_96998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106451 v h) (hints_cons _ _ _ (der_96998 v h) (by intro d hd; cases hd)))
def cl_107512 : CNF.NClause := [(146,false),(152,false),(84,false),(64,false),(38,false),(120,false),(111,false),(113,false),(102,false)]
theorem der_107512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107512 :=
  CNF.rup_sound cl_107512 [cl_106454,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106454 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107513 : CNF.NClause := [(146,false),(152,false),(84,false),(64,false),(47,false),(120,false),(99,false),(108,false),(97,false)]
theorem der_107513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107513 :=
  CNF.rup_sound cl_107513 [cl_106455,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106455 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107514 : CNF.NClause := [(146,false),(152,false),(84,false),(64,false),(55,false),(122,false),(94,false),(111,false),(107,false)]
theorem der_107514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107514 :=
  CNF.rup_sound cl_107514 [cl_106456,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106456 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107515 : CNF.NClause := [(144,false),(129,false),(86,false),(71,false),(38,false),(120,false),(104,false),(111,false),(95,false)]
theorem der_107515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107515 :=
  CNF.rup_sound cl_107515 [cl_106461,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106461 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_107519 : CNF.NClause := [(125,false),(129,false),(131,true),(141,true),(143,true),(151,true),(146,true),(32,true),(145,true)]
theorem der_107519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107519 :=
  CNF.rup_sound cl_107519 [cl_106468,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106468 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107520 : CNF.NClause := [(152,false),(132,false),(128,false),(84,false),(36,false),(117,false),(116,false),(123,false),(114,false)]
theorem der_107520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107520 :=
  CNF.rup_sound cl_107520 [cl_106469,cl_79620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106469 v h) (hints_cons _ _ _ (der_79620 v h) (by intro d hd; cases hd)))
def cl_107521 : CNF.NClause := [(125,false),(127,false),(85,false),(75,false),(58,false),(120,false),(93,false),(109,false),(100,false)]
theorem der_107521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107521 :=
  CNF.rup_sound cl_107521 [cl_106471,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106471 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107522 : CNF.NClause := [(126,false),(58,false),(127,false),(85,false),(131,true),(120,false),(93,false),(109,false),(107,false)]
theorem der_107522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107522 :=
  CNF.rup_sound cl_107522 [cl_106473,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106473 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107523 : CNF.NClause := [(125,false),(127,false),(85,false),(75,false),(47,false),(120,false),(99,false),(108,false),(115,false)]
theorem der_107523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107523 :=
  CNF.rup_sound cl_107523 [cl_106474,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106474 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107524 : CNF.NClause := [(129,false),(88,false),(142,true),(89,false),(125,true),(146,true),(62,false),(36,false),(117,true)]
theorem der_107524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107524 :=
  CNF.rup_sound cl_107524 [cl_88164,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88164 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107525 : CNF.NClause := [(135,false),(132,false),(126,false),(128,false),(84,false),(64,false),(37,false),(50,false),(104,false)]
theorem der_107525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107525 :=
  CNF.rup_sound cl_107525 [cl_106477,cl_86552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106477 v h) (hints_cons _ _ _ (der_86552 v h) (by intro d hd; cases hd)))
def cl_107526 : CNF.NClause := [(144,false),(129,false),(86,false),(71,false),(35,false),(104,false),(94,false),(118,false),(109,false)]
theorem der_107526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107526 :=
  CNF.rup_sound cl_107526 [cl_106479,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106479 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_107527 : CNF.NClause := [(135,false),(125,false),(144,false),(141,true),(86,false),(150,true),(147,true),(50,false),(102,true)]
theorem der_107527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107527 :=
  CNF.rup_sound cl_107527 [cl_106480,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106480 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_107528 : CNF.NClause := [(130,false),(150,false),(128,false),(71,false),(52,false),(104,false),(116,false),(119,false),(98,false)]
theorem der_107528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107528 :=
  CNF.rup_sound cl_107528 [cl_106482,cl_69036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106482 v h) (hints_cons _ _ _ (der_69036 v h) (by intro d hd; cases hd)))
def cl_107529 : CNF.NClause := [(135,false),(126,false),(128,false),(84,false),(45,false),(120,false),(117,false),(103,false),(101,false)]
theorem der_107529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107529 :=
  CNF.rup_sound cl_107529 [cl_106484,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106484 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_107531 : CNF.NClause := [(135,false),(152,false),(69,false),(83,false),(33,false),(118,false),(110,false),(105,false),(95,false)]
theorem der_107531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107531 :=
  CNF.rup_sound cl_107531 [cl_106486,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106486 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107532 : CNF.NClause := [(144,false),(139,false),(78,false),(71,false),(49,false),(45,false),(38,false),(37,false),(112,false)]
theorem der_107532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107532 :=
  CNF.rup_sound cl_107532 [cl_106487,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106487 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_107533 : CNF.NClause := [(146,false),(135,false),(83,false),(72,false),(52,false),(104,false),(116,false),(119,false),(110,false)]
theorem der_107533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107533 :=
  CNF.rup_sound cl_107533 [cl_106488,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106488 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107534 : CNF.NClause := [(144,false),(129,false),(86,false),(71,false),(52,false),(104,false),(119,false),(110,false),(97,false)]
theorem der_107534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107534 :=
  CNF.rup_sound cl_107534 [cl_106489,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106489 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_107536 : CNF.NClause := [(126,false),(93,false),(84,false),(64,false),(60,false),(117,false),(128,false),(111,false),(119,false)]
theorem der_107536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107536 :=
  CNF.rup_sound cl_107536 [cl_106490,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106490 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107537 : CNF.NClause := [(126,false),(43,false),(128,false),(129,false),(86,false),(71,false),(144,false),(37,false),(32,false)]
theorem der_107537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107537 :=
  CNF.rup_sound cl_107537 [cl_106491,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106491 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107538 : CNF.NClause := [(148,false),(33,false),(136,false),(83,false),(2,false),(128,false),(110,false),(105,false),(100,false)]
theorem der_107538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107538 :=
  CNF.rup_sound cl_107538 [cl_106492,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106492 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_107539 : CNF.NClause := [(146,false),(135,false),(83,false),(72,false),(35,false),(104,false),(94,false),(118,false),(99,false)]
theorem der_107539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107539 :=
  CNF.rup_sound cl_107539 [cl_106493,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106493 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107540 : CNF.NClause := [(146,false),(152,false),(84,false),(64,false),(43,false),(37,false),(55,false),(104,false),(93,false)]
theorem der_107540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107540 :=
  CNF.rup_sound cl_107540 [cl_106494,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106494 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107542 : CNF.NClause := [(135,false),(126,false),(128,false),(84,false),(37,false),(122,false),(113,false),(101,false),(97,false)]
theorem der_107542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107542 :=
  CNF.rup_sound cl_107542 [cl_106496,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106496 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_107544 : CNF.NClause := [(47,true),(918,true),(68,false),(84,false),(917,true),(89,false),(915,false),(66,false),(914,true)]
theorem der_107544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107544 :=
  CNF.rup_sound cl_107544 [cl_90292,cl_107241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_90292 v h) (hints_cons _ _ _ (der_107241 v h) (by intro d hd; cases hd)))
def cl_107545 : CNF.NClause := [(926,true),(918,true),(907,true),(75,true),(3,true),(903,true),(916,true),(900,true),(913,true)]
theorem der_107545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107545 :=
  CNF.rup_sound cl_107545 [cl_106498,cl_94890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106498 v h) (hints_cons _ _ _ (der_94890 v h) (by intro d hd; cases hd)))
def cl_107547 : CNF.NClause := [(130,false),(145,false),(131,true),(88,false),(143,true),(147,true),(58,false),(125,true),(109,true)]
theorem der_107547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107547 :=
  CNF.rup_sound cl_107547 [cl_106502,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106502 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107548 : CNF.NClause := [(146,false),(153,false),(128,false),(84,false),(76,false),(24,false),(151,true),(36,false),(115,true)]
theorem der_107548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107548 :=
  CNF.rup_sound cl_107548 [cl_106503,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106503 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107549 : CNF.NClause := [(130,false),(148,false),(128,false),(84,false),(38,false),(120,false),(104,false),(95,false),(102,false)]
theorem der_107549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107549 :=
  CNF.rup_sound cl_107549 [cl_106504,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106504 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107550 : CNF.NClause := [(135,false),(152,false),(126,false),(128,false),(79,false),(63,false),(45,false),(38,false),(50,false)]
theorem der_107550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107550 :=
  CNF.rup_sound cl_107550 [cl_106505,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106505 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107551 : CNF.NClause := [(126,false),(113,false),(84,false),(83,false),(38,false),(120,false),(111,false),(128,false),(102,false)]
theorem der_107551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107551 :=
  CNF.rup_sound cl_107551 [cl_106506,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106506 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107552 : CNF.NClause := [(146,false),(142,false),(141,true),(131,true),(129,true),(152,true),(49,true),(140,true),(137,true)]
theorem der_107552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107552 :=
  CNF.rup_sound cl_107552 [cl_106508,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106508 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107553 : CNF.NClause := [(138,false),(142,false),(131,true),(129,true),(143,true),(132,true),(128,true),(49,true),(77,false)]
theorem der_107553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107553 :=
  CNF.rup_sound cl_107553 [cl_106509,cl_86128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106509 v h) (hints_cons _ _ _ (der_86128 v h) (by intro d hd; cases hd)))
def cl_107554 : CNF.NClause := [(138,false),(142,false),(49,true),(140,true),(77,false),(125,true),(134,true),(137,true),(145,true)]
theorem der_107554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107554 :=
  CNF.rup_sound cl_107554 [cl_106510,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106510 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_107555 : CNF.NClause := [(137,false),(145,false),(79,false),(67,false),(51,false),(123,false),(99,false),(101,false),(100,false)]
theorem der_107555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107555 :=
  CNF.rup_sound cl_107555 [cl_106512,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106512 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_107556 : CNF.NClause := [(139,false),(101,false),(73,false),(75,false),(37,false),(122,false),(113,false),(134,false),(97,false)]
theorem der_107556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107556 :=
  CNF.rup_sound cl_107556 [cl_106513,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106513 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107557 : CNF.NClause := [(148,false),(136,false),(141,true),(131,true),(45,false),(120,false),(117,false),(110,false),(101,false)]
theorem der_107557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107557 :=
  CNF.rup_sound cl_107557 [cl_106514,cl_62592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106514 v h) (hints_cons _ _ _ (der_62592 v h) (by intro d hd; cases hd)))
def cl_107558 : CNF.NClause := [(153,false),(133,false),(131,true),(129,true),(46,false),(123,false),(109,false),(110,false),(108,false)]
theorem der_107558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107558 :=
  CNF.rup_sound cl_107558 [cl_106515,cl_79628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106515 v h) (hints_cons _ _ _ (der_79628 v h) (by intro d hd; cases hd)))
def cl_107559 : CNF.NClause := [(153,false),(133,false),(69,false),(63,false),(43,false),(122,false),(116,false),(103,false),(95,false)]
theorem der_107559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107559 :=
  CNF.rup_sound cl_107559 [cl_106517,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106517 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107560 : CNF.NClause := [(138,false),(139,false),(129,false),(85,false),(45,false),(120,false),(94,false),(103,false),(101,false)]
theorem der_107560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107560 :=
  CNF.rup_sound cl_107560 [cl_106518,cl_75853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106518 v h) (hints_cons _ _ _ (der_75853 v h) (by intro d hd; cases hd)))
def cl_107561 : CNF.NClause := [(138,false),(151,false),(85,false),(78,false),(51,false),(123,false),(99,false),(98,false),(102,false)]
theorem der_107561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107561 :=
  CNF.rup_sound cl_107561 [cl_106519,cl_62463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106519 v h) (hints_cons _ _ _ (der_62463 v h) (by intro d hd; cases hd)))
def cl_107562 : CNF.NClause := [(153,false),(137,false),(139,false),(14,false),(46,false),(123,false),(110,false),(112,false),(108,false)]
theorem der_107562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107562 :=
  CNF.rup_sound cl_107562 [cl_106520,cl_61595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106520 v h) (hints_cons _ _ _ (der_61595 v h) (by intro d hd; cases hd)))
def cl_107566 : CNF.NClause := [(138,false),(130,false),(128,false),(85,false),(88,false),(135,true),(49,false),(140,true),(104,true)]
theorem der_107566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107566 :=
  CNF.rup_sound cl_107566 [cl_106524,cl_62171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106524 v h) (hints_cons _ _ _ (der_62171 v h) (by intro d hd; cases hd)))
def cl_107567 : CNF.NClause := [(130,false),(136,false),(64,false),(72,false),(59,false),(39,false),(42,false),(44,false),(60,false)]
theorem der_107567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107567 :=
  CNF.rup_sound cl_107567 [cl_106525,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106525 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_107568 : CNF.NClause := [(126,false),(125,false),(131,true),(84,false),(60,false),(93,false),(99,false),(111,false),(119,false)]
theorem der_107568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107568 :=
  CNF.rup_sound cl_107568 [cl_106526,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106526 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107569 : CNF.NClause := [(135,false),(132,false),(80,false),(69,false),(36,false),(117,false),(116,false),(123,false),(115,false)]
theorem der_107569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107569 :=
  CNF.rup_sound cl_107569 [cl_106527,cl_79623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106527 v h) (hints_cons _ _ _ (der_79623 v h) (by intro d hd; cases hd)))
def cl_107570 : CNF.NClause := [(137,false),(133,false),(63,false),(45,false),(82,false),(120,false),(117,false),(110,false),(101,false)]
theorem der_107570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107570 :=
  CNF.rup_sound cl_107570 [cl_106529,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106529 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107571 : CNF.NClause := [(138,false),(146,false),(143,false),(15,false),(51,false),(123,false),(99,false),(101,false),(100,false)]
theorem der_107571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107571 :=
  CNF.rup_sound cl_107571 [cl_106531,cl_57470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106531 v h) (hints_cons _ _ _ (der_57470 v h) (by intro d hd; cases hd)))
def cl_107573 : CNF.NClause := [(151,false),(140,false),(75,false),(77,false),(39,false),(35,false),(60,false),(40,false),(116,false)]
theorem der_107573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107573 :=
  CNF.rup_sound cl_107573 [cl_106536,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106536 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_107574 : CNF.NClause := [(139,false),(134,false),(128,false),(75,false),(35,false),(94,false),(118,false),(99,false),(114,false)]
theorem der_107574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107574 :=
  CNF.rup_sound cl_107574 [cl_106537,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106537 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107576 : CNF.NClause := [(142,false),(920,false),(85,false),(79,false),(73,false),(77,false),(66,false),(35,false),(104,true)]
theorem der_107576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107576 :=
  CNF.rup_sound cl_107576 [cl_106541,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106541 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_107581 : CNF.NClause := [(146,false),(127,false),(131,true),(152,true),(135,true),(17,true),(138,true),(134,true),(137,true),(34,true)]
theorem der_107581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107581 :=
  CNF.rup_sound cl_107581 [cl_106550,cl_76531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106550 v h) (hints_cons _ _ _ (der_76531 v h) (by intro d hd; cases hd)))
def cl_107582 : CNF.NClause := [(126,false),(132,true),(134,false),(131,true),(135,true),(33,true),(141,true),(139,true),(153,true),(151,true)]
theorem der_107582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107582 :=
  CNF.rup_sound cl_107582 [cl_106551,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106551 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_107583 : CNF.NClause := [(151,false),(140,false),(78,false),(150,true),(77,false),(59,false),(104,false),(121,false),(112,false),(101,false)]
theorem der_107583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107583 :=
  CNF.rup_sound cl_107583 [cl_106553,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106553 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_107584 : CNF.NClause := [(131,false),(135,true),(134,false),(141,true),(143,true),(128,true),(147,true),(125,true),(41,true),(137,true)]
theorem der_107584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107584 :=
  CNF.rup_sound cl_107584 [cl_106555,cl_83907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106555 v h) (hints_cons _ _ _ (der_83907 v h) (by intro d hd; cases hd)))
def cl_107585 : CNF.NClause := [(126,false),(920,true),(33,true),(917,true),(909,true),(911,true),(921,true),(916,true),(131,true),(927,true)]
theorem der_107585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107585 :=
  CNF.rup_sound cl_107585 [cl_106556,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106556 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107591 : CNF.NClause := [(130,false),(151,false),(37,true),(152,true),(132,true),(74,false),(128,true),(140,true),(144,true),(66,false)]
theorem der_107591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107591 :=
  CNF.rup_sound cl_107591 [cl_106572,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106572 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_107592 : CNF.NClause := [(130,false),(139,false),(141,true),(131,true),(133,true),(77,false),(46,true),(151,true),(125,true),(148,true)]
theorem der_107592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107592 :=
  CNF.rup_sound cl_107592 [cl_106574,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106574 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107593 : CNF.NClause := [(144,false),(129,false),(86,false),(71,false),(68,false),(44,false),(109,false),(119,false),(96,false),(103,false)]
theorem der_107593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107593 :=
  CNF.rup_sound cl_107593 [cl_106575,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106575 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_107594 : CNF.NClause := [(144,false),(151,false),(139,false),(71,false),(68,false),(45,false),(120,false),(94,false),(117,false),(103,false)]
theorem der_107594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107594 :=
  CNF.rup_sound cl_107594 [cl_106576,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106576 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_107595 : CNF.NClause := [(126,false),(125,false),(131,true),(86,false),(84,false),(49,false),(122,false),(104,false),(96,false),(108,false)]
theorem der_107595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107595 :=
  CNF.rup_sound cl_107595 [cl_106577,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106577 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107596 : CNF.NClause := [(144,false),(129,false),(86,false),(71,false),(68,false),(52,false),(59,false),(39,false),(42,false),(44,false)]
theorem der_107596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107596 :=
  CNF.rup_sound cl_107596 [cl_106580,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106580 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_107597 : CNF.NClause := [(126,false),(125,false),(131,true),(86,false),(84,false),(36,false),(116,false),(123,false),(113,false),(114,false)]
theorem der_107597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107597 :=
  CNF.rup_sound cl_107597 [cl_106581,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106581 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107598 : CNF.NClause := [(146,false),(135,false),(80,false),(83,false),(72,false),(55,false),(122,false),(94,false),(107,false),(115,false)]
theorem der_107598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107598 :=
  CNF.rup_sound cl_107598 [cl_106583,cl_70161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106583 v h) (hints_cons _ _ _ (der_70161 v h) (by intro d hd; cases hd)))
def cl_107599 : CNF.NClause := [(126,false),(125,false),(131,true),(86,false),(84,false),(41,false),(104,false),(123,false),(103,false),(106,false)]
theorem der_107599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107599 :=
  CNF.rup_sound cl_107599 [cl_106584,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106584 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107600 : CNF.NClause := [(126,false),(127,false),(131,true),(85,false),(74,false),(59,false),(104,false),(93,false),(121,false),(112,false)]
theorem der_107600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107600 :=
  CNF.rup_sound cl_107600 [cl_106585,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106585 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107601 : CNF.NClause := [(139,false),(129,false),(86,false),(85,false),(18,false),(49,false),(122,false),(104,false),(96,false),(100,false)]
theorem der_107601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107601 :=
  CNF.rup_sound cl_107601 [cl_106586,cl_62455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106586 v h) (hints_cons _ _ _ (der_62455 v h) (by intro d hd; cases hd)))
def cl_107602 : CNF.NClause := [(139,false),(35,false),(134,false),(75,false),(128,false),(74,false),(94,false),(118,false),(99,false),(114,false)]
theorem der_107602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107602 :=
  CNF.rup_sound cl_107602 [cl_106587,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106587 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107604 : CNF.NClause := [(126,false),(125,false),(131,true),(86,false),(84,false),(39,false),(99,false),(113,false),(121,false),(96,false)]
theorem der_107604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107604 :=
  CNF.rup_sound cl_107604 [cl_106589,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106589 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107606 : CNF.NClause := [(126,false),(58,false),(127,false),(85,false),(131,true),(75,false),(120,false),(93,false),(109,false),(107,false)]
theorem der_107606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107606 :=
  CNF.rup_sound cl_107606 [cl_106591,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106591 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107608 : CNF.NClause := [(132,false),(84,false),(141,true),(86,false),(85,false),(142,true),(88,false),(89,false),(71,false),(143,true)]
theorem der_107608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107608 :=
  CNF.rup_sound cl_107608 [cl_106595,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106595 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_107609 : CNF.NClause := [(152,false),(132,false),(84,false),(76,false),(73,false),(33,false),(118,false),(105,false),(100,false),(95,false)]
theorem der_107609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107609 :=
  CNF.rup_sound cl_107609 [cl_106598,cl_79620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106598 v h) (hints_cons _ _ _ (der_79620 v h) (by intro d hd; cases hd)))
def cl_107610 : CNF.NClause := [(139,false),(129,false),(86,false),(85,false),(84,false),(37,false),(122,false),(101,false),(105,false),(97,false)]
theorem der_107610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107610 :=
  CNF.rup_sound cl_107610 [cl_106599,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106599 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107611 : CNF.NClause := [(126,false),(127,false),(85,false),(84,false),(64,false),(59,false),(104,false),(93,false),(121,false),(112,false)]
theorem der_107611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107611 :=
  CNF.rup_sound cl_107611 [cl_106600,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106600 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107614 : CNF.NClause := [(139,false),(129,false),(86,false),(85,false),(84,false),(59,false),(104,false),(93,false),(121,false),(101,false)]
theorem der_107614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107614 :=
  CNF.rup_sound cl_107614 [cl_106606,cl_62455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106606 v h) (hints_cons _ _ _ (der_62455 v h) (by intro d hd; cases hd)))
def cl_107615 : CNF.NClause := [(144,false),(139,false),(79,false),(71,false),(68,false),(50,false),(94,false),(116,false),(121,false),(105,false)]
theorem der_107615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107615 :=
  CNF.rup_sound cl_107615 [cl_106607,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106607 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_107617 : CNF.NClause := [(131,false),(79,false),(136,true),(89,false),(86,false),(85,false),(142,true),(84,false),(143,true),(141,true)]
theorem der_107617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107617 :=
  CNF.rup_sound cl_107617 [cl_106610,cl_95250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106610 v h) (hints_cons _ _ _ (der_95250 v h) (by intro d hd; cases hd)))
def cl_107618 : CNF.NClause := [(106,false),(144,false),(129,false),(86,false),(71,false),(34,false),(118,false),(111,false),(96,false),(128,false)]
theorem der_107618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107618 :=
  CNF.rup_sound cl_107618 [cl_106612,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106612 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_107619 : CNF.NClause := [(126,false),(141,true),(131,true),(144,false),(129,true),(135,true),(33,true),(143,true),(147,true),(137,true)]
theorem der_107619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107619 :=
  CNF.rup_sound cl_107619 [cl_106615,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106615 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_107620 : CNF.NClause := [(137,false),(145,false),(85,false),(73,false),(67,false),(50,false),(94,false),(121,false),(105,false),(108,false)]
theorem der_107620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107620 :=
  CNF.rup_sound cl_107620 [cl_106616,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106616 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107621 : CNF.NClause := [(137,false),(145,false),(85,false),(73,false),(67,false),(45,false),(120,false),(94,false),(117,false),(101,false)]
theorem der_107621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107621 :=
  CNF.rup_sound cl_107621 [cl_106618,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106618 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107622 : CNF.NClause := [(138,false),(135,false),(132,false),(142,false),(139,false),(134,false),(75,false),(49,false),(122,false),(117,false)]
theorem der_107622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107622 :=
  CNF.rup_sound cl_107622 [cl_106619,cl_72081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106619 v h) (hints_cons _ _ _ (der_72081 v h) (by intro d hd; cases hd)))
def cl_107623 : CNF.NClause := [(135,false),(77,false),(85,false),(69,false),(49,false),(143,false),(122,false),(104,false),(117,false),(96,false)]
theorem der_107623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107623 :=
  CNF.rup_sound cl_107623 [cl_106620,cl_79623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106620 v h) (hints_cons _ _ _ (der_79623 v h) (by intro d hd; cases hd)))
def cl_107624 : CNF.NClause := [(138,false),(127,false),(85,false),(128,false),(83,false),(45,false),(120,false),(117,false),(110,false),(103,false)]
theorem der_107624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107624 :=
  CNF.rup_sound cl_107624 [cl_106621,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106621 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_107625 : CNF.NClause := [(126,false),(127,false),(85,false),(84,false),(75,false),(43,false),(122,false),(99,false),(103,false),(112,false)]
theorem der_107625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107625 :=
  CNF.rup_sound cl_107625 [cl_106622,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106622 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107626 : CNF.NClause := [(138,false),(42,false),(127,false),(85,false),(83,false),(128,false),(121,false),(103,false),(100,false),(97,false)]
theorem der_107626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107626 :=
  CNF.rup_sound cl_107626 [cl_106623,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106623 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_107627 : CNF.NClause := [(139,false),(49,false),(73,false),(75,false),(134,false),(74,false),(122,false),(117,false),(96,false),(100,false)]
theorem der_107627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107627 :=
  CNF.rup_sound cl_107627 [cl_106624,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106624 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107628 : CNF.NClause := [(138,false),(151,false),(137,false),(152,true),(80,false),(150,true),(74,false),(39,false),(113,false),(121,false)]
theorem der_107628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107628 :=
  CNF.rup_sound cl_107628 [cl_106625,cl_79624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106625 v h) (hints_cons _ _ _ (der_79624 v h) (by intro d hd; cases hd)))
def cl_107629 : CNF.NClause := [(923,true),(907,true),(909,true),(926,true),(915,true),(911,true),(905,true),(928,true),(88,true),(913,true)]
theorem der_107629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107629 :=
  CNF.rup_sound cl_107629 [cl_99003,cl_107244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_99003 v h) (hints_cons _ _ _ (der_107244 v h) (by intro d hd; cases hd)))
def cl_107631 : CNF.NClause := [(139,false),(134,false),(73,false),(75,false),(74,false),(55,false),(122,false),(94,false),(98,false),(115,false)]
theorem der_107631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107631 :=
  CNF.rup_sound cl_107631 [cl_106628,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106628 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107632 : CNF.NClause := [(138,false),(125,false),(128,false),(23,false),(65,false),(74,false),(67,false),(47,false),(41,false),(51,false)]
theorem der_107632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107632 :=
  CNF.rup_sound cl_107632 [cl_106629,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106629 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_107633 : CNF.NClause := [(138,false),(125,false),(127,false),(85,false),(75,false),(57,false),(122,false),(93,false),(110,false),(114,false)]
theorem der_107633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107633 :=
  CNF.rup_sound cl_107633 [cl_106630,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106630 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_107634 : CNF.NClause := [(138,false),(147,false),(81,false),(65,false),(43,false),(42,true),(122,false),(116,false),(99,false),(95,false)]
theorem der_107634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107634 :=
  CNF.rup_sound cl_107634 [cl_106631,cl_76537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106631 v h) (hints_cons _ _ _ (der_76537 v h) (by intro d hd; cases hd)))
def cl_107637 : CNF.NClause := [(139,false),(50,false),(76,false),(75,false),(74,false),(134,false),(94,false),(116,false),(121,false),(102,false)]
theorem der_107637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107637 :=
  CNF.rup_sound cl_107637 [cl_106634,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106634 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_107639 : CNF.NClause := [(139,false),(116,false),(73,false),(75,false),(74,false),(58,false),(120,false),(134,false),(93,false),(100,false)]
theorem der_107639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107639 :=
  CNF.rup_sound cl_107639 [cl_106636,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106636 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107641 : CNF.NClause := [(138,false),(126,false),(125,false),(76,false),(64,false),(55,false),(122,false),(94,false),(111,false),(98,false)]
theorem der_107641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107641 :=
  CNF.rup_sound cl_107641 [cl_106638,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106638 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107642 : CNF.NClause := [(153,false),(136,false),(145,false),(141,true),(152,true),(71,false),(151,true),(53,false),(109,false),(121,false)]
theorem der_107642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107642 :=
  CNF.rup_sound cl_107642 [cl_106640,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106640 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107643 : CNF.NClause := [(138,false),(145,false),(133,false),(69,false),(73,false),(38,false),(120,false),(111,false),(95,false),(102,false)]
theorem der_107643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107643 :=
  CNF.rup_sound cl_107643 [cl_106641,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106641 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107644 : CNF.NClause := [(133,false),(141,false),(70,false),(77,false),(82,false),(53,false),(117,false),(109,false),(121,false),(98,false)]
theorem der_107644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107644 :=
  CNF.rup_sound cl_107644 [cl_106643,cl_79619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106643 v h) (hints_cons _ _ _ (der_79619 v h) (by intro d hd; cases hd)))
def cl_107645 : CNF.NClause := [(138,false),(145,false),(141,false),(83,false),(46,false),(77,false),(123,false),(111,false),(109,false),(112,false)]
theorem der_107645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107645 :=
  CNF.rup_sound cl_107645 [cl_106644,cl_79619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106644 v h) (hints_cons _ _ _ (der_79619 v h) (by intro d hd; cases hd)))
def cl_107649 : CNF.NClause := [(145,false),(133,false),(131,true),(129,true),(81,false),(39,false),(99,false),(121,false),(96,false),(107,false)]
theorem der_107649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107649 :=
  CNF.rup_sound cl_107649 [cl_106648,cl_94030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106648 v h) (hints_cons _ _ _ (der_94030 v h) (by intro d hd; cases hd)))
def cl_107650 : CNF.NClause := [(144,false),(51,true),(141,false),(138,true),(150,true),(151,true),(125,true),(148,true),(126,true),(145,true)]
theorem der_107650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107650 :=
  CNF.rup_sound cl_107650 [cl_106649,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106649 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_107653 : CNF.NClause := [(91,false),(80,false),(84,false),(76,false),(64,false),(63,false),(21,true),(20,true),(55,true),(23,true),(53,false)]
theorem der_107653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107653 :=
  CNF.rup_sound cl_107653 [cl_106653,cl_107231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106653 v h) (hints_cons _ _ _ (der_107231 v h) (by intro d hd; cases hd)))
def cl_107655 : CNF.NClause := [(81,true),(910,true),(917,true),(926,true),(919,false),(912,true),(915,true),(911,true),(904,true),(15,true),(923,true)]
theorem der_107655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107655 :=
  CNF.rup_sound cl_107655 [cl_66817,cl_107243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66817 v h) (hints_cons _ _ _ (der_107243 v h) (by intro d hd; cases hd)))
def cl_107657 : CNF.NClause := [(126,false),(93,false),(131,true),(79,false),(83,false),(74,false),(60,false),(117,false),(128,false),(111,false),(119,false)]
theorem der_107657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107657 :=
  CNF.rup_sound cl_107657 [cl_106662,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106662 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107658 : CNF.NClause := [(144,false),(129,false),(86,false),(85,false),(84,false),(83,false),(48,false),(119,false),(108,false),(107,false),(95,false)]
theorem der_107658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107658 :=
  CNF.rup_sound cl_107658 [cl_106663,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106663 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_107659 : CNF.NClause := [(151,false),(98,false),(140,false),(78,false),(68,false),(75,false),(55,false),(122,false),(94,false),(111,false),(141,true)]
theorem der_107659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107659 :=
  CNF.rup_sound cl_107659 [cl_106664,cl_65889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106664 v h) (hints_cons _ _ _ (der_65889 v h) (by intro d hd; cases hd)))
def cl_107667 : CNF.NClause := [(144,false),(129,false),(86,false),(83,false),(70,false),(71,false),(38,false),(120,false),(104,false),(111,false),(95,false)]
theorem der_107667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107667 :=
  CNF.rup_sound cl_107667 [cl_106681,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106681 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_107669 : CNF.NClause := [(144,false),(129,false),(86,false),(83,false),(70,false),(71,false),(59,false),(104,false),(93,false),(121,false),(112,false)]
theorem der_107669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107669 :=
  CNF.rup_sound cl_107669 [cl_106690,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106690 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_107673 : CNF.NClause := [(139,false),(129,false),(86,false),(85,false),(84,false),(78,false),(35,false),(104,false),(94,false),(118,false),(99,false)]
theorem der_107673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107673 :=
  CNF.rup_sound cl_107673 [cl_106696,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106696 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107674 : CNF.NClause := [(144,false),(129,false),(86,false),(83,false),(71,false),(68,false),(38,false),(59,false),(39,false),(42,false),(98,false)]
theorem der_107674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107674 :=
  CNF.rup_sound cl_107674 [cl_106699,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106699 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_107675 : CNF.NClause := [(125,false),(127,false),(85,false),(80,false),(70,false),(75,false),(46,false),(123,false),(109,false),(110,false),(108,false)]
theorem der_107675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107675 :=
  CNF.rup_sound cl_107675 [cl_106701,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106701 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107677 : CNF.NClause := [(126,false),(107,false),(127,false),(85,false),(84,false),(75,false),(41,false),(104,false),(123,false),(103,false),(79,false)]
theorem der_107677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107677 :=
  CNF.rup_sound cl_107677 [cl_106706,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106706 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107679 : CNF.NClause := [(152,false),(143,false),(141,true),(142,true),(63,false),(74,false),(58,false),(120,false),(109,false),(100,false),(107,false)]
theorem der_107679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107679 :=
  CNF.rup_sound cl_107679 [cl_106709,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106709 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107680 : CNF.NClause := [(136,false),(142,false),(85,false),(73,false),(64,false),(77,false),(60,false),(93,false),(111,false),(119,false),(105,false)]
theorem der_107680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107680 :=
  CNF.rup_sound cl_107680 [cl_106710,cl_61053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106710 v h) (hints_cons _ _ _ (der_61053 v h) (by intro d hd; cases hd)))
def cl_107681 : CNF.NClause := [(130,false),(136,false),(64,false),(81,false),(72,false),(59,false),(82,false),(104,false),(93,false),(121,false),(115,false)]
theorem der_107681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107681 :=
  CNF.rup_sound cl_107681 [cl_106712,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106712 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_107682 : CNF.NClause := [(104,false),(89,false),(147,false),(129,false),(86,false),(69,false),(71,false),(38,false),(144,false),(111,false),(95,false)]
theorem der_107682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107682 :=
  CNF.rup_sound cl_107682 [cl_106715,cl_85177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106715 v h) (hints_cons _ _ _ (der_85177 v h) (by intro d hd; cases hd)))
def cl_107686 : CNF.NClause := [(140,true),(21,false),(71,false),(76,false),(1,false),(132,true),(136,false),(144,true),(66,false),(53,false),(117,true)]
theorem der_107686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107686 :=
  CNF.rup_sound cl_107686 [cl_106733,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106733 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107688 : CNF.NClause := [(89,false),(142,false),(147,false),(139,false),(141,true),(144,false),(143,true),(49,false),(122,false),(104,false),(117,false)]
theorem der_107688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107688 :=
  CNF.rup_sound cl_107688 [cl_106737,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106737 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107689 : CNF.NClause := [(136,false),(150,false),(141,true),(152,true),(71,false),(64,false),(46,false),(123,false),(111,false),(109,false),(108,false)]
theorem der_107689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107689 :=
  CNF.rup_sound cl_107689 [cl_106738,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106738 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107690 : CNF.NClause := [(136,false),(150,false),(141,true),(152,true),(71,false),(64,false),(53,false),(117,false),(109,false),(121,false),(98,false)]
theorem der_107690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107690 :=
  CNF.rup_sound cl_107690 [cl_106739,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106739 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107691 : CNF.NClause := [(138,false),(130,false),(152,false),(142,false),(137,false),(75,false),(151,true),(59,false),(121,false),(112,false),(115,false)]
theorem der_107691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107691 :=
  CNF.rup_sound cl_107691 [cl_106742,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106742 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107692 : CNF.NClause := [(138,false),(131,false),(134,false),(78,false),(15,false),(81,false),(75,false),(77,false),(94,false),(117,false),(101,false)]
theorem der_107692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107692 :=
  CNF.rup_sound cl_107692 [cl_106743,cl_83907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106743 v h) (hints_cons _ _ _ (der_83907 v h) (by intro d hd; cases hd)))
def cl_107697 : CNF.NClause := [(125,false),(43,false),(84,false),(69,false),(2,false),(64,false),(49,false),(79,false),(37,false),(55,false),(50,false)]
theorem der_107697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107697 :=
  CNF.rup_sound cl_107697 [cl_106758,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106758 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107699 : CNF.NClause := [(153,false),(89,false),(137,false),(152,true),(80,false),(76,false),(150,true),(39,false),(113,false),(121,false),(110,false)]
theorem der_107699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107699 :=
  CNF.rup_sound cl_107699 [cl_106763,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106763 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_107700 : CNF.NClause := [(126,false),(127,false),(85,false),(84,false),(64,false),(75,false),(60,false),(117,false),(93,false),(99,false),(119,false)]
theorem der_107700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107700 :=
  CNF.rup_sound cl_107700 [cl_106766,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106766 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107701 : CNF.NClause := [(67,true),(901,true),(917,true),(908,true),(914,false),(903,true),(904,true),(925,true),(916,true),(912,true),(905,true)]
theorem der_107701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107701 :=
  CNF.rup_sound cl_107701 [cl_106767,cl_62077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106767 v h) (hints_cons _ _ _ (der_62077 v h) (by intro d hd; cases hd)))
def cl_107702 : CNF.NClause := [(126,false),(125,false),(131,true),(86,false),(84,false),(44,false),(47,false),(120,false),(99,false),(108,false),(106,false)]
theorem der_107702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107702 :=
  CNF.rup_sound cl_107702 [cl_106769,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106769 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_107704 : CNF.NClause := [(146,false),(126,false),(125,false),(153,false),(145,false),(71,false),(73,false),(81,false),(53,false),(35,false),(116,false)]
theorem der_107704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107704 :=
  CNF.rup_sound cl_107704 [cl_106770,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106770 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107705 : CNF.NClause := [(151,false),(6,true),(64,false),(21,true),(75,false),(90,false),(67,false),(20,true),(109,true),(66,false),(35,false)]
theorem der_107705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107705 :=
  CNF.rup_sound cl_107705 [cl_106771,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106771 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_107706 : CNF.NClause := [(137,false),(145,false),(128,false),(90,false),(138,true),(134,true),(136,true),(35,false),(94,false),(118,false),(99,false)]
theorem der_107706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107706 :=
  CNF.rup_sound cl_107706 [cl_106773,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106773 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107707 : CNF.NClause := [(146,false),(151,false),(128,false),(125,false),(85,false),(80,false),(70,false),(7,false),(64,false),(3,false),(39,false)]
theorem der_107707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107707 :=
  CNF.rup_sound cl_107707 [cl_106775,cl_102901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106775 v h) (hints_cons _ _ _ (der_102901 v h) (by intro d hd; cases hd)))
def cl_107710 : CNF.NClause := [(43,true),(59,false),(55,true),(54,false),(44,false),(50,false),(94,false),(48,false),(109,false),(119,false),(103,false),(101,false)]
theorem der_107710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107710 :=
  CNF.rup_sound cl_107710 [cl_106782,cl_76560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106782 v h) (hints_cons _ _ _ (der_76560 v h) (by intro d hd; cases hd)))
def cl_107711 : CNF.NClause := [(85,false),(65,false),(80,false),(70,false),(3,false),(128,false),(75,false),(55,false),(122,false),(98,false),(107,false),(115,false)]
theorem der_107711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107711 :=
  CNF.rup_sound cl_107711 [cl_106786,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106786 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_107712 : CNF.NClause := [(125,false),(141,false),(85,false),(80,false),(3,false),(75,false),(65,false),(48,false),(119,false),(114,false),(108,false),(95,false)]
theorem der_107712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107712 :=
  CNF.rup_sound cl_107712 [cl_106787,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106787 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107714 : CNF.NClause := [(43,false),(5,false),(86,false),(85,false),(84,false),(83,false),(134,false),(82,false),(122,false),(99,false),(112,false),(95,false)]
theorem der_107714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107714 :=
  CNF.rup_sound cl_107714 [cl_106788,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106788 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_107715 : CNF.NClause := [(126,false),(108,false),(131,true),(84,false),(45,true),(83,false),(74,false),(50,false),(116,false),(121,false),(128,false),(102,false)]
theorem der_107715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107715 :=
  CNF.rup_sound cl_107715 [cl_106789,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106789 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107716 : CNF.NClause := [(80,false),(85,false),(128,false),(70,false),(3,false),(75,false),(65,false),(45,false),(120,false),(117,false),(110,false),(103,false)]
theorem der_107716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107716 :=
  CNF.rup_sound cl_107716 [cl_106790,cl_88575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106790 v h) (hints_cons _ _ _ (der_88575 v h) (by intro d hd; cases hd)))
def cl_107717 : CNF.NClause := [(129,false),(69,false),(70,false),(71,false),(68,false),(67,false),(20,false),(53,false),(109,false),(121,false),(106,false),(95,false)]
theorem der_107717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107717 :=
  CNF.rup_sound cl_107717 [cl_106791,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106791 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107718 : CNF.NClause := [(129,false),(69,false),(70,false),(71,false),(68,false),(34,false),(67,false),(20,false),(118,false),(111,false),(96,false),(106,false)]
theorem der_107718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107718 :=
  CNF.rup_sound cl_107718 [cl_106792,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106792 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107719 : CNF.NClause := [(126,false),(125,false),(131,true),(79,false),(86,false),(84,false),(74,false),(40,false),(94,false),(113,false),(119,false),(106,false)]
theorem der_107719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107719 :=
  CNF.rup_sound cl_107719 [cl_106793,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106793 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107720 : CNF.NClause := [(81,true),(909,true),(910,true),(915,true),(902,true),(15,true),(919,true),(901,true),(906,true),(923,true),(900,true),(913,true)]
theorem der_107720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107720 :=
  CNF.rup_sound cl_107720 [cl_66834,cl_107243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66834 v h) (hints_cons _ _ _ (der_107243 v h) (by intro d hd; cases hd)))
def cl_107721 : CNF.NClause := [(137,false),(116,false),(69,false),(63,false),(81,false),(75,false),(9,false),(43,false),(82,false),(122,false),(99,false),(95,false)]
theorem der_107721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107721 :=
  CNF.rup_sound cl_107721 [cl_106794,cl_80955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106794 v h) (hints_cons _ _ _ (der_80955 v h) (by intro d hd; cases hd)))
def cl_107722 : CNF.NClause := [(125,false),(86,false),(127,false),(85,false),(80,false),(75,false),(38,true),(44,false),(109,false),(119,false),(103,false),(115,false)]
theorem der_107722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107722 :=
  CNF.rup_sound cl_107722 [cl_106795,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106795 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107723 : CNF.NClause := [(127,false),(78,false),(83,false),(73,false),(68,false),(63,false),(4,false),(54,false),(120,false),(112,false),(105,false),(98,false)]
theorem der_107723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107723 :=
  CNF.rup_sound cl_107723 [cl_106797,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106797 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_107724 : CNF.NClause := [(146,false),(125,false),(89,false),(127,false),(78,false),(69,false),(29,false),(27,false),(40,false),(94,false),(113,false),(119,false)]
theorem der_107724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107724 :=
  CNF.rup_sound cl_107724 [cl_106801,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106801 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107725 : CNF.NClause := [(125,false),(78,false),(83,false),(73,false),(68,false),(63,false),(4,false),(36,false),(116,false),(123,false),(113,false),(115,false)]
theorem der_107725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107725 :=
  CNF.rup_sound cl_107725 [cl_106804,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106804 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107726 : CNF.NClause := [(146,false),(125,false),(127,false),(85,false),(39,true),(80,false),(48,true),(41,false),(104,false),(123,false),(103,false),(105,false)]
theorem der_107726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107726 :=
  CNF.rup_sound cl_107726 [cl_106806,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106806 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107727 : CNF.NClause := [(153,false),(121,false),(88,false),(78,false),(152,true),(76,false),(150,true),(39,false),(113,false),(89,false),(110,false),(96,false)]
theorem der_107727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107727 :=
  CNF.rup_sound cl_107727 [cl_106812,cl_62562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106812 v h) (hints_cons _ _ _ (der_62562 v h) (by intro d hd; cases hd)))
def cl_107729 : CNF.NClause := [(129,false),(69,false),(70,false),(71,false),(68,false),(67,false),(20,false),(59,false),(104,false),(93,false),(121,false),(112,false)]
theorem der_107729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107729 :=
  CNF.rup_sound cl_107729 [cl_106816,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106816 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107730 : CNF.NClause := [(129,false),(69,false),(70,false),(71,false),(68,false),(43,false),(67,false),(20,false),(122,false),(103,false),(112,false),(95,false)]
theorem der_107730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107730 :=
  CNF.rup_sound cl_107730 [cl_106817,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106817 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107731 : CNF.NClause := [(144,false),(70,false),(135,true),(134,false),(71,false),(138,true),(75,false),(37,false),(122,false),(109,false),(113,false),(97,false)]
theorem der_107731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107731 :=
  CNF.rup_sound cl_107731 [cl_106818,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106818 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_107732 : CNF.NClause := [(122,false),(5,false),(86,false),(85,false),(84,false),(83,false),(82,false),(55,false),(134,false),(94,false),(111,false),(98,false)]
theorem der_107732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107732 :=
  CNF.rup_sound cl_107732 [cl_106819,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106819 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_107733 : CNF.NClause := [(120,false),(5,false),(86,false),(85,false),(84,false),(83,false),(45,false),(82,false),(134,false),(94,false),(110,false),(101,false)]
theorem der_107733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107733 :=
  CNF.rup_sound cl_107733 [cl_106821,cl_93560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106821 v h) (hints_cons _ _ _ (der_93560 v h) (by intro d hd; cases hd)))
def cl_107735 : CNF.NClause := [(129,false),(69,false),(70,false),(71,false),(68,false),(67,false),(20,false),(38,false),(120,false),(104,false),(111,false),(95,false)]
theorem der_107735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107735 :=
  CNF.rup_sound cl_107735 [cl_106824,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106824 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107740 : CNF.NClause := [(53,false),(109,false),(85,false),(84,false),(83,false),(75,false),(5,false),(82,false),(134,false),(121,false),(98,false),(95,false)]
theorem der_107740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107740 :=
  CNF.rup_sound cl_107740 [cl_106829,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106829 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107741 : CNF.NClause := [(142,false),(27,false),(26,false),(83,false),(71,false),(75,false),(79,false),(47,false),(120,false),(99,false),(97,false),(115,false)]
theorem der_107741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107741 :=
  CNF.rup_sound cl_107741 [cl_106831,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106831 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_107742 : CNF.NClause := [(130,false),(62,false),(26,false),(83,false),(71,false),(75,false),(53,false),(79,false),(117,false),(121,false),(98,false),(95,false)]
theorem der_107742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107742 :=
  CNF.rup_sound cl_107742 [cl_106832,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106832 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107744 : CNF.NClause := [(125,false),(85,false),(80,false),(70,false),(3,false),(75,false),(65,false),(51,false),(123,false),(99,false),(100,false),(98,false)]
theorem der_107744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107744 :=
  CNF.rup_sound cl_107744 [cl_106834,cl_93569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106834 v h) (hints_cons _ _ _ (der_93569 v h) (by intro d hd; cases hd)))
def cl_107745 : CNF.NClause := [(125,false),(65,false),(80,false),(70,false),(3,false),(75,false),(85,false),(38,false),(120,false),(104,false),(113,false),(95,false)]
theorem der_107745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107745 :=
  CNF.rup_sound cl_107745 [cl_106835,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106835 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107746 : CNF.NClause := [(148,false),(79,false),(26,false),(83,false),(71,false),(75,false),(46,false),(62,false),(123,false),(109,false),(112,false),(108,false)]
theorem der_107746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107746 :=
  CNF.rup_sound cl_107746 [cl_106836,cl_66108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106836 v h) (hints_cons _ _ _ (der_66108 v h) (by intro d hd; cases hd)))
def cl_107747 : CNF.NClause := [(130,false),(79,false),(26,false),(83,false),(71,false),(75,false),(38,false),(62,false),(120,false),(104,false),(111,false),(95,false)]
theorem der_107747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107747 :=
  CNF.rup_sound cl_107747 [cl_106837,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106837 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_107748 : CNF.NClause := [(130,false),(79,false),(26,false),(83,false),(71,false),(75,false),(62,false),(41,false),(104,false),(123,false),(103,false),(107,false)]
theorem der_107748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107748 :=
  CNF.rup_sound cl_107748 [cl_106838,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106838 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_107750 : CNF.NClause := [(148,false),(39,false),(150,false),(79,false),(84,false),(71,false),(75,false),(128,false),(99,false),(113,false),(121,false),(96,false)]
theorem der_107750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107750 :=
  CNF.rup_sound cl_107750 [cl_106840,cl_85704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106840 v h) (hints_cons _ _ _ (der_85704 v h) (by intro d hd; cases hd)))
def cl_107753 : CNF.NClause := [(144,false),(129,false),(143,false),(86,false),(80,false),(11,false),(77,false),(45,false),(72,false),(38,false),(59,false),(66,false)]
theorem der_107753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107753 :=
  CNF.rup_sound cl_107753 [cl_106844,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106844 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_107754 : CNF.NClause := [(152,false),(55,false),(71,false),(63,false),(74,false),(77,false),(19,false),(85,false),(122,false),(111,false),(98,false),(107,false)]
theorem der_107754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107754 :=
  CNF.rup_sound cl_107754 [cl_106846,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106846 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107756 : CNF.NClause := [(130,false),(84,false),(80,false),(76,false),(63,false),(24,false),(67,false),(38,false),(33,false),(35,false),(41,false),(51,false)]
theorem der_107756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107756 :=
  CNF.rup_sound cl_107756 [cl_106848,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106848 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107758 : CNF.NClause := [(118,false),(89,false),(141,true),(140,false),(134,false),(79,false),(142,true),(143,true),(35,false),(94,false),(128,false),(114,false)]
theorem der_107758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107758 :=
  CNF.rup_sound cl_107758 [cl_106851,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106851 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_107763 : CNF.NClause := [(142,false),(107,false),(15,false),(12,false),(68,false),(64,false),(72,false),(39,false),(113,false),(121,false),(110,false),(85,false)]
theorem der_107763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107763 :=
  CNF.rup_sound cl_107763 [cl_106857,cl_105458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106857 v h) (hints_cons _ _ _ (der_105458 v h) (by intro d hd; cases hd)))
def cl_107765 : CNF.NClause := [(135,false),(70,false),(129,false),(85,false),(143,false),(68,false),(77,false),(67,false),(20,false),(59,false),(39,false),(117,false)]
theorem der_107765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107765 :=
  CNF.rup_sound cl_107765 [cl_106860,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106860 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107766 : CNF.NClause := [(129,false),(69,false),(70,false),(71,false),(68,false),(67,false),(20,false),(45,false),(58,false),(38,false),(54,false),(55,false)]
theorem der_107766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107766 :=
  CNF.rup_sound cl_107766 [cl_94514,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_94514 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107767 : CNF.NClause := [(135,false),(38,false),(85,false),(80,false),(71,false),(49,false),(77,false),(45,false),(58,false),(143,false),(66,false),(37,false)]
theorem der_107767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107767 :=
  CNF.rup_sound cl_107767 [cl_106861,cl_79623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106861 v h) (hints_cons _ _ _ (der_79623 v h) (by intro d hd; cases hd)))
def cl_107769 : CNF.NClause := [(126,false),(138,true),(136,false),(84,false),(83,false),(76,false),(143,true),(128,false),(133,true),(39,false),(42,false),(37,false)]
theorem der_107769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107769 :=
  CNF.rup_sound cl_107769 [cl_106864,cl_56868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106864 v h) (hints_cons _ _ _ (der_56868 v h) (by intro d hd; cases hd)))
def cl_107771 : CNF.NClause := [(132,false),(142,false),(141,true),(131,true),(69,false),(73,false),(143,true),(49,true),(151,true),(134,true),(144,true),(137,true)]
theorem der_107771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107771 :=
  CNF.rup_sound cl_107771 [cl_106866,cl_93676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106866 v h) (hints_cons _ _ _ (der_93676 v h) (by intro d hd; cases hd)))
def cl_107772 : CNF.NClause := [(135,false),(126,false),(128,false),(143,false),(131,true),(79,false),(85,false),(69,false),(43,false),(77,false),(122,false),(112,false)]
theorem der_107772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107772 :=
  CNF.rup_sound cl_107772 [cl_106867,cl_79623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106867 v h) (hints_cons _ _ _ (der_79623 v h) (by intro d hd; cases hd)))
def cl_107776 : CNF.NClause := [(136,false),(142,false),(15,false),(69,false),(73,false),(64,false),(46,false),(77,false),(123,false),(111,false),(109,false),(110,false)]
theorem der_107776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107776 :=
  CNF.rup_sound cl_107776 [cl_106871,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106871 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107780 : CNF.NClause := [(138,false),(148,false),(142,false),(23,false),(84,false),(73,false),(77,false),(54,false),(120,false),(112,false),(114,false),(105,false)]
theorem der_107780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107780 :=
  CNF.rup_sound cl_107780 [cl_106876,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106876 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_107786 : CNF.NClause := [(145,false),(133,false),(69,false),(73,false),(63,false),(75,false),(82,false),(42,false),(111,false),(121,false),(103,false),(114,false)]
theorem der_107786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107786 :=
  CNF.rup_sound cl_107786 [cl_106886,cl_56741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106886 v h) (hints_cons _ _ _ (der_56741 v h) (by intro d hd; cases hd)))
def cl_107788 : CNF.NClause := [(86,false),(90,false),(141,true),(22,false),(78,false),(64,false),(53,true),(133,true),(132,true),(128,true),(140,true),(137,true),(136,true)]
theorem der_107788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107788 :=
  CNF.rup_sound cl_107788 [cl_106888,cl_96266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106888 v h) (hints_cons _ _ _ (der_96266 v h) (by intro d hd; cases hd)))
def cl_107790 : CNF.NClause := [(125,false),(54,true),(80,false),(70,false),(3,false),(75,false),(85,false),(65,false),(59,false),(104,false),(93,false),(121,false),(115,false)]
theorem der_107790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107790 :=
  CNF.rup_sound cl_107790 [cl_106889,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106889 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107791 : CNF.NClause := [(139,false),(119,false),(76,false),(73,false),(75,false),(74,false),(72,false),(10,false),(60,false),(117,false),(93,false),(99,false),(141,true)]
theorem der_107791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107791 :=
  CNF.rup_sound cl_107791 [cl_106890,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106890 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107792 : CNF.NClause := [(126,false),(94,false),(86,false),(71,false),(76,false),(81,false),(1,false),(66,false),(40,false),(131,true),(113,false),(119,false),(106,false)]
theorem der_107792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107792 :=
  CNF.rup_sound cl_107792 [cl_106891,cl_103219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106891 v h) (hints_cons _ _ _ (der_103219 v h) (by intro d hd; cases hd)))
def cl_107794 : CNF.NClause := [(130,false),(84,false),(80,false),(128,false),(76,false),(24,false),(74,false),(67,false),(38,false),(120,false),(104,false),(95,false),(102,false)]
theorem der_107794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107794 :=
  CNF.rup_sound cl_107794 [cl_106896,cl_62574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106896 v h) (hints_cons _ _ _ (der_62574 v h) (by intro d hd; cases hd)))
def cl_107795 : CNF.NClause := [(125,false),(79,false),(84,false),(69,false),(71,false),(2,false),(64,false),(74,false),(40,false),(94,false),(113,false),(119,false),(106,false)]
theorem der_107795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107795 :=
  CNF.rup_sound cl_107795 [cl_106901,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106901 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_107796 : CNF.NClause := [(125,false),(86,false),(79,false),(84,false),(69,false),(2,false),(64,false),(74,false),(55,false),(122,false),(94,false),(111,false),(98,false)]
theorem der_107796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107796 :=
  CNF.rup_sound cl_107796 [cl_106902,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106902 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107800 : CNF.NClause := [(127,false),(98,false),(84,false),(69,false),(70,false),(2,false),(64,false),(74,false),(51,false),(123,false),(99,false),(79,false),(102,false)]
theorem der_107800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107800 :=
  CNF.rup_sound cl_107800 [cl_106906,cl_76532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106906 v h) (hints_cons _ _ _ (der_76532 v h) (by intro d hd; cases hd)))
def cl_107802 : CNF.NClause := [(142,false),(12,false),(85,false),(68,false),(64,false),(81,false),(77,false),(72,false),(44,false),(109,false),(119,false),(115,false),(102,false)]
theorem der_107802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107802 :=
  CNF.rup_sound cl_107802 [cl_106908,cl_86128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106908 v h) (hints_cons _ _ _ (der_86128 v h) (by intro d hd; cases hd)))
def cl_107804 : CNF.NClause := [(125,false),(86,false),(84,false),(69,false),(71,false),(2,false),(64,false),(74,false),(59,false),(39,false),(42,false),(117,false),(102,false)]
theorem der_107804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107804 :=
  CNF.rup_sound cl_107804 [cl_106910,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106910 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_107811 : CNF.NClause := [(125,false),(79,false),(86,false),(84,false),(69,false),(2,false),(64,false),(74,false),(38,false),(120,false),(104,false),(111,false),(113,false)]
theorem der_107811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107811 :=
  CNF.rup_sound cl_107811 [cl_106917,cl_61806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106917 v h) (hints_cons _ _ _ (der_61806 v h) (by intro d hd; cases hd)))
def cl_107813 : CNF.NClause := [(152,false),(136,false),(142,false),(85,false),(69,false),(71,false),(64,false),(63,false),(74,false),(45,false),(19,false),(42,false),(54,false)]
theorem der_107813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107813 :=
  CNF.rup_sound cl_107813 [cl_106919,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106919 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107817 : CNF.NClause := [(66,false),(80,false),(11,false),(69,false),(83,false),(77,false),(45,false),(72,false),(143,false),(120,false),(117,false),(110,false),(101,false)]
theorem der_107817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107817 :=
  CNF.rup_sound cl_107817 [cl_106923,cl_63480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106923 v h) (hints_cons _ _ _ (der_63480 v h) (by intro d hd; cases hd)))
def cl_107818 : CNF.NClause := [(135,false),(132,false),(125,false),(79,false),(86,false),(84,false),(69,false),(2,false),(64,false),(74,false),(38,false),(120,false),(104,false)]
theorem der_107818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107818 :=
  CNF.rup_sound cl_107818 [cl_106924,cl_86552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106924 v h) (hints_cons _ _ _ (der_86552 v h) (by intro d hd; cases hd)))
def cl_107820 : CNF.NClause := [(144,false),(111,false),(71,false),(73,false),(68,false),(75,false),(67,false),(72,false),(38,false),(120,false),(134,false),(113,false),(95,false)]
theorem der_107820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107820 :=
  CNF.rup_sound cl_107820 [cl_106926,cl_56888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106926 v h) (hints_cons _ _ _ (der_56888 v h) (by intro d hd; cases hd)))
def cl_107823 : CNF.NClause := [(66,false),(36,false),(80,false),(11,false),(69,false),(83,false),(143,false),(72,false),(85,false),(117,false),(123,false),(113,false),(115,false)]
theorem der_107823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107823 :=
  CNF.rup_sound cl_107823 [cl_106930,cl_107208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106930 v h) (hints_cons _ _ _ (der_107208 v h) (by intro d hd; cases hd)))
def cl_107838 : CNF.NClause := [(130,false),(135,false),(132,false),(85,false),(12,false),(69,false),(68,false),(64,false),(81,false),(38,true),(33,false),(118,false),(115,false)]
theorem der_107838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107838 :=
  CNF.rup_sound cl_107838 [cl_106954,cl_79623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106954 v h) (hints_cons _ _ _ (der_79623 v h) (by intro d hd; cases hd)))
def cl_107840 : CNF.NClause := [(138,false),(151,false),(89,false),(133,false),(78,false),(152,true),(80,false),(68,false),(150,true),(46,false),(82,false),(123,false),(108,false)]
theorem der_107840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107840 :=
  CNF.rup_sound cl_107840 [cl_106956,cl_79621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106956 v h) (hints_cons _ _ _ (der_79621 v h) (by intro d hd; cases hd)))
def cl_107843 : CNF.NClause := [(151,false),(110,false),(140,false),(90,false),(142,true),(71,false),(63,false),(139,true),(57,false),(122,false),(141,true),(114,false),(106,false)]
theorem der_107843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107843 :=
  CNF.rup_sound cl_107843 [cl_106959,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106959 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_107844 : CNF.NClause := [(151,false),(136,false),(128,false),(150,false),(79,false),(80,false),(71,false),(7,false),(64,false),(82,false),(35,false),(94,false),(118,false)]
theorem der_107844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107844 :=
  CNF.rup_sound cl_107844 [cl_106960,cl_65751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106960 v h) (hints_cons _ _ _ (der_65751 v h) (by intro d hd; cases hd)))
def cl_107846 : CNF.NClause := [(142,false),(84,false),(80,false),(76,false),(73,false),(63,false),(24,false),(67,false),(35,false),(118,false),(99,false),(109,false),(114,false)]
theorem der_107846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107846 :=
  CNF.rup_sound cl_107846 [cl_106963,cl_63405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106963 v h) (hints_cons _ _ _ (der_63405 v h) (by intro d hd; cases hd)))
def cl_107847 : CNF.NClause := [(79,false),(89,false),(14,false),(83,false),(70,false),(63,false),(72,false),(33,false),(82,false),(36,false),(118,false),(105,false),(100,false),(95,false)]
theorem der_107847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107847 :=
  CNF.rup_sound cl_107847 [cl_79192,cl_107286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79192 v h) (hints_cons _ _ _ (der_107286 v h) (by intro d hd; cases hd)))
def cl_107849 : CNF.NClause := [(132,false),(60,false),(85,false),(71,false),(63,false),(54,true),(74,false),(77,false),(19,false),(90,false),(117,false),(93,false),(111,false),(119,false)]
theorem der_107849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107849 :=
  CNF.rup_sound cl_107849 [cl_106966,cl_67721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106966 v h) (hints_cons _ _ _ (der_67721 v h) (by intro d hd; cases hd)))
def cl_107851 : CNF.NClause := [(125,false),(64,false),(79,false),(84,false),(69,false),(2,false),(141,true),(74,false),(57,true),(53,false),(51,false),(123,false),(99,false),(101,false)]
theorem der_107851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107851 :=
  CNF.rup_sound cl_107851 [cl_106968,cl_93559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106968 v h) (hints_cons _ _ _ (der_93559 v h) (by intro d hd; cases hd)))
def cl_107852 : CNF.NClause := [(121,false),(88,false),(84,false),(13,false),(78,false),(71,false),(81,false),(72,false),(42,false),(54,false),(111,false),(89,false),(100,false),(97,false)]
theorem der_107852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107852 :=
  CNF.rup_sound cl_107852 [cl_79212,cl_107248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79212 v h) (hints_cons _ _ _ (der_107248 v h) (by intro d hd; cases hd)))
def cl_107853 : CNF.NClause := [(89,false),(23,false),(83,false),(71,false),(76,false),(2,false),(1,false),(49,false),(67,false),(57,false),(33,false),(66,false),(53,false),(120,false)]
theorem der_107853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107853 :=
  CNF.rup_sound cl_107853 [cl_106972,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106972 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107854 : CNF.NClause := [(53,false),(69,false),(83,false),(70,false),(71,false),(68,false),(67,false),(20,false),(85,false),(36,false),(109,false),(121,false),(106,false),(95,false)]
theorem der_107854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107854 :=
  CNF.rup_sound cl_107854 [cl_66565,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66565 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107856 : CNF.NClause := [(137,false),(88,false),(89,false),(23,false),(78,false),(83,false),(81,false),(74,false),(67,false),(55,false),(122,false),(94,false),(111,false),(107,false)]
theorem der_107856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107856 :=
  CNF.rup_sound cl_107856 [cl_106976,cl_61980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106976 v h) (hints_cons _ _ _ (der_61980 v h) (by intro d hd; cases hd)))
def cl_107859 : CNF.NClause := [(79,false),(80,false),(18,false),(78,false),(15,false),(144,false),(71,false),(68,false),(81,false),(39,false),(113,false),(121,false),(96,false),(107,false)]
theorem der_107859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107859 :=
  CNF.rup_sound cl_107859 [cl_106982,cl_62696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106982 v h) (hints_cons _ _ _ (der_62696 v h) (by intro d hd; cases hd)))
def cl_107861 : CNF.NClause := [(146,false),(150,false),(85,false),(152,true),(12,false),(71,false),(68,false),(81,false),(72,false),(35,false),(104,false),(94,false),(118,false),(109,false)]
theorem der_107861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107861 :=
  CNF.rup_sound cl_107861 [cl_106984,cl_85132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106984 v h) (hints_cons _ _ _ (der_85132 v h) (by intro d hd; cases hd)))
def cl_107862 : CNF.NClause := [(79,false),(77,false),(78,false),(15,false),(80,false),(81,false),(75,false),(134,false),(72,false),(40,false),(94,false),(113,false),(119,false),(100,false)]
theorem der_107862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107862 :=
  CNF.rup_sound cl_107862 [cl_106985,cl_98860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106985 v h) (hints_cons _ _ _ (der_98860 v h) (by intro d hd; cases hd)))
def cl_107865 : CNF.NClause := [(18,false),(79,false),(144,false),(78,false),(15,false),(80,false),(71,false),(68,false),(81,false),(45,false),(120,false),(94,false),(117,false),(103,false)]
theorem der_107865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107865 :=
  CNF.rup_sound cl_107865 [cl_106988,cl_79626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106988 v h) (hints_cons _ _ _ (der_79626 v h) (by intro d hd; cases hd)))
def cl_107867 : CNF.NClause := [(70,false),(39,false),(71,false),(76,false),(74,false),(67,false),(20,false),(45,false),(72,false),(128,false),(10,false),(33,false),(53,false),(35,false)]
theorem der_107867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107867 :=
  CNF.rup_sound cl_107867 [cl_106990,cl_107233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106990 v h) (hints_cons _ _ _ (der_107233 v h) (by intro d hd; cases hd)))
def cl_107870 : CNF.NClause := [(139,false),(39,false),(141,true),(134,false),(142,true),(78,false),(73,false),(143,true),(75,false),(74,false),(89,false),(113,false),(121,false),(96,false)]
theorem der_107870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107870 :=
  CNF.rup_sound cl_107870 [cl_106994,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106994 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107871 : CNF.NClause := [(130,false),(142,false),(143,false),(85,false),(78,false),(80,false),(11,false),(69,false),(83,false),(43,false),(77,false),(45,false),(72,false),(38,false)]
theorem der_107871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107871 :=
  CNF.rup_sound cl_107871 [cl_106995,cl_62573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_106995 v h) (hints_cons _ _ _ (der_62573 v h) (by intro d hd; cases hd)))
def cl_107874 : CNF.NClause := [(152,false),(125,false),(139,false),(131,true),(79,false),(90,false),(13,false),(143,true),(150,true),(151,true),(37,false),(122,false),(113,false),(97,false)]
theorem der_107874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107874 :=
  CNF.rup_sound cl_107874 [cl_107001,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107001 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_107877 : CNF.NClause := [(125,false),(79,false),(85,false),(68,false),(63,false),(8,false),(49,false),(74,false),(43,false),(82,false),(19,false),(37,false),(32,false),(110,false)]
theorem der_107877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107877 :=
  CNF.rup_sound cl_107877 [cl_107005,cl_107181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107005 v h) (hints_cons _ _ _ (der_107181 v h) (by intro d hd; cases hd)))
def cl_107878 : CNF.NClause := [(130,false),(84,false),(78,false),(80,false),(76,false),(63,false),(24,false),(1,false),(67,false),(59,false),(42,false),(54,false),(35,false),(32,false)]
theorem der_107878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107878 :=
  CNF.rup_sound cl_107878 [cl_107006,cl_67570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107006 v h) (hints_cons _ _ _ (der_67570 v h) (by intro d hd; cases hd)))
def cl_107883 : CNF.NClause := [(148,false),(84,false),(78,false),(80,false),(70,false),(6,false),(1,false),(74,false),(67,false),(39,false),(99,false),(121,false),(110,false),(96,false)]
theorem der_107883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107883 :=
  CNF.rup_sound cl_107883 [cl_107014,cl_63761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107014 v h) (hints_cons _ _ _ (der_63761 v h) (by intro d hd; cases hd)))
def cl_107887 : CNF.NClause := [(137,false),(139,false),(88,false),(135,true),(76,false),(73,false),(138,true),(75,false),(74,false),(136,true),(50,false),(94,false),(116,false),(121,false)]
theorem der_107887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107887 :=
  CNF.rup_sound cl_107887 [cl_107018,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107018 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107889 : CNF.NClause := [(95,false),(78,false),(83,false),(73,false),(14,true),(68,false),(63,false),(4,false),(87,false),(53,false),(32,false),(121,false),(98,false),(106,false),(79,false)]
theorem der_107889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107889 :=
  CNF.rup_sound cl_107889 [cl_39898,cl_107183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39898 v h) (hints_cons _ _ _ (der_107183 v h) (by intro d hd; cases hd)))
def cl_107891 : CNF.NClause := [(66,false),(136,false),(131,true),(78,false),(70,false),(6,false),(72,false),(10,false),(52,false),(82,false),(141,true),(104,false),(119,false),(110,false),(98,false)]
theorem der_107891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107891 :=
  CNF.rup_sound cl_107891 [cl_107022,cl_93799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107022 v h) (hints_cons _ _ _ (der_93799 v h) (by intro d hd; cases hd)))
def cl_107892 : CNF.NClause := [(142,false),(120,false),(70,false),(6,false),(74,false),(44,true),(77,false),(58,false),(5,true),(82,false),(66,false),(78,false),(116,false),(93,false),(107,false)]
theorem der_107892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107892 :=
  CNF.rup_sound cl_107892 [cl_107023,cl_83925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107023 v h) (hints_cons _ _ _ (der_83925 v h) (by intro d hd; cases hd)))
def cl_107896 : CNF.NClause := [(146,false),(39,false),(84,false),(91,false),(70,false),(63,false),(3,false),(24,false),(1,false),(43,false),(49,true),(59,false),(85,false),(32,false),(106,false)]
theorem der_107896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107896 :=
  CNF.rup_sound cl_107896 [cl_107029,cl_79636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107029 v h) (hints_cons _ _ _ (der_79636 v h) (by intro d hd; cases hd)))
def cl_107899 : CNF.NClause := [(139,false),(5,false),(86,false),(85,false),(84,false),(78,false),(80,false),(83,false),(53,true),(82,false),(44,false),(119,false),(96,false),(103,false),(102,false)]
theorem der_107899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107899 :=
  CNF.rup_sound cl_107899 [cl_107032,cl_72397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107032 v h) (hints_cons _ _ _ (der_72397 v h) (by intro d hd; cases hd)))
def cl_107910 : CNF.NClause := [(151,false),(74,false),(86,false),(152,true),(80,false),(29,false),(68,false),(133,false),(150,true),(58,false),(82,false),(120,false),(116,false),(109,false),(107,false)]
theorem der_107910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107910 :=
  CNF.rup_sound cl_107910 [cl_107051,cl_62149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107051 v h) (hints_cons _ _ _ (der_62149 v h) (by intro d hd; cases hd)))
def cl_107913 : CNF.NClause := [(90,false),(141,true),(85,false),(18,true),(78,false),(83,false),(70,false),(71,false),(76,false),(64,false),(63,false),(46,false),(74,false),(16,true),(108,true)]
theorem der_107913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107913 :=
  CNF.rup_sound cl_107913 [cl_107058,cl_107271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107058 v h) (hints_cons _ _ _ (der_107271 v h) (by intro d hd; cases hd)))
def cl_107916 : CNF.NClause := [(98,false),(79,false),(80,false),(69,false),(2,false),(28,false),(64,false),(3,false),(65,false),(74,false),(38,true),(53,false),(117,false),(109,false),(121,false),(85,false)]
theorem der_107916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107916 :=
  CNF.rup_sound cl_107916 [cl_79302,cl_107231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79302 v h) (hints_cons _ _ _ (der_107231 v h) (by intro d hd; cases hd)))
def cl_107917 : CNF.NClause := [(54,true),(85,false),(12,false),(70,false),(68,false),(64,false),(81,false),(6,false),(74,false),(48,true),(52,false),(59,false),(82,false),(44,false),(53,false),(99,false)]
theorem der_107917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107917 :=
  CNF.rup_sound cl_107917 [cl_107064,cl_107230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107064 v h) (hints_cons _ _ _ (der_107230 v h) (by intro d hd; cases hd)))
def cl_107922 : CNF.NClause := [(130,false),(135,false),(85,false),(84,false),(12,false),(83,false),(73,false),(28,false),(68,false),(64,false),(81,false),(72,false),(58,false),(62,false),(120,false),(107,false)]
theorem der_107922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107922 :=
  CNF.rup_sound cl_107922 [cl_107071,cl_82115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107071 v h) (hints_cons _ _ _ (der_82115 v h) (by intro d hd; cases hd)))
def cl_107929 : CNF.NClause := [(923,true),(913,true),(129,false),(85,false),(69,false),(75,false),(917,true),(922,true),(39,false),(915,true),(925,true),(906,true),(128,false),(133,false),(914,true),(113,true)]
theorem der_107929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107929 :=
  CNF.rup_sound cl_107929 [cl_107079,cl_107222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107079 v h) (hints_cons _ _ _ (der_107222 v h) (by intro d hd; cases hd)))
def cl_107930 : CNF.NClause := [(86,false),(115,false),(78,false),(69,false),(64,false),(75,false),(67,false),(72,false),(52,false),(42,false),(47,false),(34,true),(40,false),(120,false),(99,false),(108,false),(22,false)]
theorem der_107930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107930 :=
  CNF.rup_sound cl_107930 [cl_79330,cl_107340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79330 v h) (hints_cons _ _ _ (der_107340 v h) (by intro d hd; cases hd)))
def cl_107932 : CNF.NClause := [(86,false),(108,false),(22,false),(78,false),(64,false),(8,false),(75,false),(28,true),(65,false),(20,false),(41,true),(82,false),(48,false),(119,false),(101,false),(114,false),(79,false)]
theorem der_107932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107932 :=
  CNF.rup_sound cl_107932 [cl_79341,cl_107198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79341 v h) (hints_cons _ _ _ (der_107198 v h) (by intro d hd; cases hd)))
def cl_107942 : CNF.NClause := [(126,false),(143,true),(84,false),(78,false),(80,false),(11,false),(70,false),(76,false),(64,false),(128,false),(138,true),(6,false),(133,true),(67,false),(38,false),(39,false),(42,false)]
theorem der_107942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107942 :=
  CNF.rup_sound cl_107942 [cl_107096,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107096 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107948 : CNF.NClause := [(146,false),(147,false),(141,true),(140,false),(142,true),(45,true),(129,true),(83,false),(71,false),(3,false),(65,false),(74,false),(153,true),(50,false),(94,false),(116,false),(121,false)]
theorem der_107948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107948 :=
  CNF.rup_sound cl_107948 [cl_107107,cl_102901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107107 v h) (hints_cons _ _ _ (der_102901 v h) (by intro d hd; cases hd)))
def cl_107952 : CNF.NClause := [(151,false),(143,true),(139,false),(141,true),(140,false),(131,true),(152,true),(135,true),(128,false),(132,true),(147,true),(50,true),(58,false),(130,true),(125,true),(144,true),(137,true),(47,false)]
theorem der_107952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107952 :=
  CNF.rup_sound cl_107952 [cl_107111,cl_88464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107111 v h) (hints_cons _ _ _ (der_88464 v h) (by intro d hd; cases hd)))
def cl_107956 : CNF.NClause := [(126,false),(138,true),(89,false),(147,false),(84,false),(12,false),(80,false),(76,false),(63,false),(143,true),(128,false),(81,false),(133,true),(41,true),(39,false),(34,true),(113,false),(121,false)]
theorem der_107956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107956 :=
  CNF.rup_sound cl_107956 [cl_107116,cl_68805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107116 v h) (hints_cons _ _ _ (der_68805 v h) (by intro d hd; cases hd)))
def cl_107983 : CNF.NClause := [(131,false),(86,false),(85,false),(84,false),(12,false),(83,false),(76,false),(68,false),(81,false),(75,false),(133,true),(92,false),(132,true),(74,false),(34,false),(10,false),(82,false),(118,false),(111,false),(96,false),(101,false)]
theorem der_107983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107983 :=
  CNF.rup_sound cl_107983 [cl_107146,cl_83907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107146 v h) (hints_cons _ _ _ (der_83907 v h) (by intro d hd; cases hd)))
def cl_107990 : CNF.NClause := [(130,false),(136,false),(79,false),(86,false),(142,true),(84,false),(152,true),(69,false),(83,false),(71,false),(2,false),(64,false),(139,true),(138,true),(133,true),(147,true),(67,false),(20,false),(153,true),(72,false),(146,true),(42,false)]
theorem der_107990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107990 :=
  CNF.rup_sound cl_107990 [cl_107153,cl_76535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107153 v h) (hints_cons _ _ _ (der_76535 v h) (by intro d hd; cases hd)))
def cl_107992 : CNF.NClause := [(86,true),(911,true),(14,true),(926,true),(915,true),(88,true),(1081,true),(1063,true),(1070,true),(905,true),(1071,true),(906,true),(1072,true),(928,true),(1077,true),(923,true),(1060,true),(1067,true),(1078,true),(1066,true),(1082,false),(1075,true)]
theorem der_107992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107992 :=
  CNF.rup_sound cl_107992 [cl_104988,cl_107244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_104988 v h) (hints_cons _ _ _ (der_107244 v h) (by intro d hd; cases hd)))
def cl_107997 : CNF.NClause := [(130,false),(152,false),(126,false),(153,false),(131,true),(79,false),(86,false),(85,false),(142,true),(91,false),(80,false),(83,false),(139,true),(143,true),(138,true),(133,true),(43,false),(140,true),(151,true),(146,true),(134,true),(59,false),(42,false)]
theorem der_107997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_107997 :=
  CNF.rup_sound cl_107997 [cl_107158,cl_95606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_107158 v h) (hints_cons _ _ _ (der_95606 v h) (by intro d hd; cases hd)))
def cl_108022 : CNF.NClause := [(84,true),(33,false),(79,false)]
theorem der_108022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108022 :=
  CNF.rup_sound cl_108022 [cl_105970,cl_107254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105970 v h) (hints_cons _ _ _ (der_107254 v h) (by intro d hd; cases hd)))
def cl_108023 : CNF.NClause := [(33,false),(74,true),(79,false)]
theorem der_108023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108023 :=
  CNF.rup_sound cl_108023 [cl_79970,cl_107254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79970 v h) (hints_cons _ _ _ (der_107254 v h) (by intro d hd; cases hd)))
def cl_108024 : CNF.NClause := [(60,false),(80,false),(74,true)]
theorem der_108024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108024 :=
  CNF.rup_sound cl_108024 [cl_105872,cl_107251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_105872 v h) (hints_cons _ _ _ (der_107251 v h) (by intro d hd; cases hd)))
def cl_108025 : CNF.NClause := [(135,true),(150,true),(153,true),(49,false),(133,false),(146,true),(131,true),(141,true),(129,true),(84,false),(114,false),(139,false),(80,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108025 :=
  CNF.rup_sound cl_108025 [cl_15770,cl_106128,cl_101685,cl_105154,cl_8114,cl_107282,cl_76732,cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_76759,cl_15784,cl_105770,cl_76725,cl_15781,cl_105797,cl_8021,cl_62286,cl_62171,cl_88575,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_105769,cl_80918,cl_78004,cl_107341,cl_93676,cl_79629,cl_8099,cl_105554,cl_15789,cl_107388,cl_76761,cl_76665,cl_107574,cl_8050,cl_105609,cl_15782,cl_15630,cl_15647,cl_49762,cl_70063,cl_105781,cl_107711,cl_62910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (inp_8114 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (der_76732 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (inp_8099 v h) (hints_cons _ _ _ (der_105554 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_107388 v h) (hints_cons _ _ _ (der_76761 v h) (hints_cons _ _ _ (der_76665 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (inp_8050 v h) (hints_cons _ _ _ (der_105609 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15630 v h) (hints_cons _ _ _ (der_15647 v h) (hints_cons _ _ _ (der_49762 v h) (hints_cons _ _ _ (der_70063 v h) (hints_cons _ _ _ (der_105781 v h) (hints_cons _ _ _ (der_107711 v h) (hints_cons _ _ _ (der_62910 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108026 : CNF.NClause := [(153,true),(49,false),(133,false),(146,true),(131,true),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108026 :=
  CNF.rup_sound cl_108026 [cl_15775,cl_15770,cl_106128,cl_101685,cl_61659,cl_15781,cl_105154,cl_15784,cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_79495,cl_15620,cl_8114,cl_107282,cl_108025,cl_107296,cl_76658,cl_42476,cl_64116,cl_76558,cl_7948,cl_76730,cl_79677,cl_41521,cl_107389,cl_107309,cl_15649,cl_15779,cl_105771,cl_35284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (inp_8114 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (der_108025 v h) (hints_cons _ _ _ (der_107296 v h) (hints_cons _ _ _ (der_76658 v h) (hints_cons _ _ _ (der_42476 v h) (hints_cons _ _ _ (der_64116 v h) (hints_cons _ _ _ (der_76558 v h) (hints_cons _ _ _ (inp_7948 v h) (hints_cons _ _ _ (der_76730 v h) (hints_cons _ _ _ (der_79677 v h) (hints_cons _ _ _ (der_41521 v h) (hints_cons _ _ _ (der_107389 v h) (hints_cons _ _ _ (der_107309 v h) (hints_cons _ _ _ (der_15649 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_105771 v h) (hints_cons _ _ _ (der_35284 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))
def cl_108027 : CNF.NClause := [(49,false),(146,true),(131,true),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108027 :=
  CNF.rup_sound cl_108027 [cl_76564,cl_42866,cl_49841,cl_76759,cl_50033,cl_76725,cl_105154,cl_15770,cl_106128,cl_88560,cl_107246,cl_105769,cl_80918,cl_105775,cl_107341,cl_78004,cl_62286,cl_62171,cl_88575,cl_88464,cl_62965,cl_76779,cl_101685,cl_105696,cl_15775,cl_15781,cl_105797,cl_105458,cl_93676,cl_107245,cl_107276,cl_79495,cl_79629,cl_107355,cl_50022,cl_108026,cl_15794,cl_67558,cl_88594,cl_15617,cl_65851,cl_49837,cl_107382,cl_7681,cl_76720,cl_76735,cl_76664,cl_76715,cl_50040,cl_62276,cl_7963,cl_106289,cl_94328,cl_76975,cl_15785,cl_107282,cl_8022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_42866 v h) (hints_cons _ _ _ (der_49841 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_105696 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_107355 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (der_108026 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_67558 v h) (hints_cons _ _ _ (der_88594 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_65851 v h) (hints_cons _ _ _ (der_49837 v h) (hints_cons _ _ _ (der_107382 v h) (hints_cons _ _ _ (inp_7681 v h) (hints_cons _ _ _ (der_76720 v h) (hints_cons _ _ _ (der_76735 v h) (hints_cons _ _ _ (der_76664 v h) (hints_cons _ _ _ (der_76715 v h) (hints_cons _ _ _ (der_50040 v h) (hints_cons _ _ _ (der_62276 v h) (hints_cons _ _ _ (inp_7963 v h) (hints_cons _ _ _ (der_106289 v h) (hints_cons _ _ _ (der_94328 v h) (hints_cons _ _ _ (der_76975 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (inp_8022 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108028 : CNF.NClause := [(146,true),(131,true),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108028 :=
  CNF.rup_sound cl_108028 [cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_76759,cl_105154,cl_15784,cl_105770,cl_76725,cl_15781,cl_105797,cl_15770,cl_106128,cl_101685,cl_8021,cl_61659,cl_62286,cl_62171,cl_88575,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_105769,cl_80918,cl_78004,cl_107341,cl_105458,cl_93676,cl_83925,cl_42866,cl_49841,cl_76564,cl_79495,cl_105696,cl_108027,cl_105801,cl_105799,cl_59715,cl_49814,cl_15778,cl_15790,cl_15791,cl_15630,cl_15617,cl_8114,cl_8078,cl_107282,cl_15777,cl_107296,cl_76732,cl_64116,cl_107649,cl_8108,cl_15642,cl_8027,cl_8043,cl_15779,cl_92696,cl_106151,cl_105245,cl_84166,cl_64190,cl_49856,cl_76806,cl_49863,cl_76917,cl_7946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_42866 v h) (hints_cons _ _ _ (der_49841 v h) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_105696 v h) (hints_cons _ _ _ (der_108027 v h) (hints_cons _ _ _ (der_105801 v h) (hints_cons _ _ _ (der_105799 v h) (hints_cons _ _ _ (der_59715 v h) (hints_cons _ _ _ (der_49814 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15630 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (inp_8114 v h) (hints_cons _ _ _ (inp_8078 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (der_15777 v h) (hints_cons _ _ _ (der_107296 v h) (hints_cons _ _ _ (der_76732 v h) (hints_cons _ _ _ (der_64116 v h) (hints_cons _ _ _ (der_107649 v h) (hints_cons _ _ _ (inp_8108 v h) (hints_cons _ _ _ (der_15642 v h) (hints_cons _ _ _ (inp_8027 v h) (hints_cons _ _ _ (inp_8043 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_92696 v h) (hints_cons _ _ _ (der_106151 v h) (hints_cons _ _ _ (der_105245 v h) (hints_cons _ _ _ (der_84166 v h) (hints_cons _ _ _ (der_64190 v h) (hints_cons _ _ _ (der_49856 v h) (hints_cons _ _ _ (der_76806 v h) (hints_cons _ _ _ (der_49863 v h) (hints_cons _ _ _ (der_76917 v h) (hints_cons _ _ _ (inp_7946 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108029 : CNF.NClause := [(137,false),(110,false),(150,true),(132,false),(133,false),(148,true),(121,false),(131,true),(141,true),(129,true),(151,true),(144,true),(139,false),(3,false),(86,false),(39,false),(128,false)]
theorem der_108029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108029 :=
  CNF.rup_sound cl_108029 [cl_15781,cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_62965,cl_49882,cl_98939,cl_76732,cl_98908,cl_107282,cl_8025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_98939 v h) (hints_cons _ _ _ (der_76732 v h) (hints_cons _ _ _ (der_98908 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (inp_8025 v h) (by intro d hd; cases hd)))))))))))))))
def cl_108030 : CNF.NClause := [(49,true),(133,false),(148,true),(146,false),(131,true),(138,true),(141,true),(129,true),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108030 :=
  CNF.rup_sound cl_108030 [cl_76759,cl_105154,cl_15784,cl_105770,cl_15656,cl_88560,cl_107246,cl_107245,cl_105073,cl_47827,cl_76737,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_35634,cl_50033,cl_107276,cl_76725,cl_15781,cl_105797,cl_8021,cl_49882,cl_76779,cl_105769,cl_80918,cl_107341,cl_105458,cl_93676,cl_83925,cl_76564,cl_105801,cl_105799,cl_49814,cl_15778,cl_15791,cl_15626,cl_15617,cl_67569,cl_107366,cl_8078,cl_36748,cl_108029,cl_107552,cl_15649,cl_105620,cl_107602,cl_104732,cl_99488,cl_54971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_15656 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_105073 v h) (hints_cons _ _ _ (der_47827 v h) (hints_cons _ _ _ (der_76737 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_105801 v h) (hints_cons _ _ _ (der_105799 v h) (hints_cons _ _ _ (der_49814 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15626 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_67569 v h) (hints_cons _ _ _ (der_107366 v h) (hints_cons _ _ _ (inp_8078 v h) (hints_cons _ _ _ (der_36748 v h) (hints_cons _ _ _ (der_108029 v h) (hints_cons _ _ _ (der_107552 v h) (hints_cons _ _ _ (der_15649 v h) (hints_cons _ _ _ (der_105620 v h) (hints_cons _ _ _ (der_107602 v h) (hints_cons _ _ _ (der_104732 v h) (hints_cons _ _ _ (der_99488 v h) (hints_cons _ _ _ (der_54971 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108031 : CNF.NClause := [(133,false),(148,true),(146,false),(131,true),(138,true),(141,true),(129,true),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108031 :=
  CNF.rup_sound cl_108031 [cl_88560,cl_107246,cl_107245,cl_105073,cl_47827,cl_76737,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_35634,cl_15788,cl_50033,cl_107276,cl_76759,cl_105154,cl_15784,cl_105770,cl_76725,cl_15781,cl_105797,cl_8021,cl_49882,cl_76779,cl_105769,cl_80918,cl_107341,cl_106128,cl_105458,cl_93676,cl_83925,cl_76564,cl_108030,cl_50022,cl_7941,cl_105195,cl_76677,cl_54971,cl_15787,cl_107383,cl_106151,cl_15643,cl_8109,cl_15779,cl_15626,cl_8105,cl_107366,cl_105620,cl_36748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_105073 v h) (hints_cons _ _ _ (der_47827 v h) (hints_cons _ _ _ (der_76737 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_15788 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_108030 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (inp_7941 v h) (hints_cons _ _ _ (der_105195 v h) (hints_cons _ _ _ (der_76677 v h) (hints_cons _ _ _ (der_54971 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_107383 v h) (hints_cons _ _ _ (der_106151 v h) (hints_cons _ _ _ (der_15643 v h) (hints_cons _ _ _ (inp_8109 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_15626 v h) (hints_cons _ _ _ (inp_8105 v h) (hints_cons _ _ _ (der_107366 v h) (hints_cons _ _ _ (der_105620 v h) (hints_cons _ _ _ (der_36748 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108032 : CNF.NClause := [(131,true),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108032 :=
  CNF.rup_sound cl_108032 [cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_76759,cl_105154,cl_15784,cl_105770,cl_76725,cl_15781,cl_105797,cl_15770,cl_106128,cl_101685,cl_8021,cl_62286,cl_62171,cl_88575,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_105769,cl_80918,cl_107341,cl_108028,cl_63071,cl_105073,cl_35634,cl_107846,cl_15790,cl_108031,cl_15625,cl_105330,cl_15657,cl_107574,cl_107502,cl_7941,cl_8057,cl_50022,cl_8024,cl_105799,cl_107501,cl_15778,cl_67205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_108028 v h) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_105073 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_107846 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_108031 v h) (hints_cons _ _ _ (der_15625 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (der_15657 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (inp_7941 v h) (hints_cons _ _ _ (inp_8057 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (inp_8024 v h) (hints_cons _ _ _ (der_105799 v h) (hints_cons _ _ _ (der_107501 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_67205 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108033 : CNF.NClause := [(148,true),(145,true),(134,true),(132,false),(133,true),(64,false),(127,true),(141,true),(129,true),(84,false),(151,true),(139,false),(85,false),(3,false),(71,false),(142,false),(96,false),(39,false),(128,false)]
theorem der_108033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108033 :=
  CNF.rup_sound cl_108033 [cl_101685,cl_61659,cl_15781,cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_62965,cl_105458,cl_83925,cl_15784,cl_107246,cl_105769,cl_80918,cl_79495,cl_79629,cl_15625,cl_8056,cl_15785,cl_67563,cl_8108,cl_107282,cl_15778,cl_107389,cl_105799,cl_76663,cl_50022,cl_49731,cl_94328,cl_107623,cl_102587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_15625 v h) (hints_cons _ _ _ (inp_8056 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_67563 v h) (hints_cons _ _ _ (inp_8108 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_107389 v h) (hints_cons _ _ _ (der_105799 v h) (hints_cons _ _ _ (der_76663 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (der_49731 v h) (hints_cons _ _ _ (der_94328 v h) (hints_cons _ _ _ (der_107623 v h) (hints_cons _ _ _ (der_102587 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))
def cl_108034 : CNF.NClause := [(137,false),(133,true),(131,false),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(118,false),(70,false),(75,false),(85,false),(3,false),(80,false),(71,false),(130,true),(152,true),(142,false),(51,true),(96,false),(39,false),(128,false)]
theorem der_108034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108034 :=
  CNF.rup_sound cl_108034 [cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_62965,cl_49882,cl_15784,cl_107246,cl_107245,cl_101685,cl_105330,cl_107574,cl_15658,cl_88579,cl_15773,cl_15781,cl_105797,cl_8021,cl_105458,cl_93676,cl_83925,cl_105769,cl_80918,cl_79495,cl_107501,cl_108033,cl_15790,cl_80957,cl_59715,cl_107846,cl_70013,cl_50022,cl_35634,cl_49725,cl_106285,cl_107287,cl_39659,cl_105793,cl_15620,cl_15641,cl_50718,cl_8048,cl_76537,cl_49761,cl_105475,cl_89486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_15658 v h) (hints_cons _ _ _ (der_88579 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_107501 v h) (hints_cons _ _ _ (der_108033 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_80957 v h) (hints_cons _ _ _ (der_59715 v h) (hints_cons _ _ _ (der_107846 v h) (hints_cons _ _ _ (der_70013 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_49725 v h) (hints_cons _ _ _ (der_106285 v h) (hints_cons _ _ _ (der_107287 v h) (hints_cons _ _ _ (der_39659 v h) (hints_cons _ _ _ (der_105793 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_15641 v h) (hints_cons _ _ _ (der_50718 v h) (hints_cons _ _ _ (inp_8048 v h) (hints_cons _ _ _ (der_76537 v h) (hints_cons _ _ _ (der_49761 v h) (hints_cons _ _ _ (der_105475 v h) (hints_cons _ _ _ (der_89486 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108035 : CNF.NClause := [(145,true),(146,true),(55,false),(148,false),(137,true),(134,true),(133,true),(131,false),(138,true),(141,true),(129,true),(151,true),(144,true),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108035 :=
  CNF.rup_sound cl_108035 [cl_54642,cl_105154,cl_83925,cl_93676,cl_62171,cl_88560,cl_107246,cl_105769,cl_80918,cl_105458,cl_15784,cl_15790,cl_59715,cl_15773,cl_107245,cl_50033,cl_107276,cl_76759,cl_105770,cl_8021,cl_62286,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_49882,cl_79629,cl_15662,cl_15641,cl_15617,cl_15789,cl_8046,cl_49761,cl_105787,cl_105387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54642 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_59715 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_15662 v h) (hints_cons _ _ _ (der_15641 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (inp_8046 v h) (hints_cons _ _ _ (der_49761 v h) (hints_cons _ _ _ (der_105787 v h) (hints_cons _ _ _ (der_105387 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))
def cl_108036 : CNF.NClause := [(150,false),(21,false),(146,true),(134,true),(133,true),(131,false),(127,true),(84,false),(151,true),(81,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108036 :=
  CNF.rup_sound cl_108036 [cl_88560,cl_107246,cl_105769,cl_80918,cl_15770,cl_106128,cl_78004,cl_107245,cl_50033,cl_107276,cl_62171,cl_15791,cl_15620,cl_8046,cl_36500,cl_15794,cl_15782,cl_49836,cl_105447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (inp_8046 v h) (hints_cons _ _ _ (der_36500 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_49836 v h) (hints_cons _ _ _ (der_105447 v h) (by intro d hd; cases hd))))))))))))))))))))
def cl_108037 : CNF.NClause := [(148,false),(133,true),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108037 :=
  CNF.rup_sound cl_108037 [cl_76564,cl_76725,cl_105154,cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_76759,cl_15784,cl_105770,cl_105775,cl_15770,cl_106128,cl_105769,cl_80918,cl_107341,cl_78004,cl_62286,cl_62171,cl_88575,cl_88464,cl_62965,cl_76779,cl_108032,cl_108034,cl_49882,cl_101685,cl_105330,cl_107574,cl_88579,cl_15773,cl_15781,cl_105797,cl_8021,cl_61659,cl_105458,cl_93676,cl_83925,cl_79495,cl_79629,cl_15790,cl_80957,cl_107388,cl_59715,cl_107846,cl_49969,cl_76665,cl_50022,cl_35634,cl_44574,cl_107287,cl_54218,cl_108035,cl_15787,cl_60437,cl_108036,cl_8048,cl_15617,cl_8101,cl_8114,cl_15768,cl_67569,cl_107400,cl_15767,cl_107282,cl_76340,cl_53892,cl_49843,cl_105390,cl_49731,cl_76756,cl_94328,cl_49761,cl_107377,cl_32081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_108032 v h) (hints_cons _ _ _ (der_108034 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_88579 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_80957 v h) (hints_cons _ _ _ (der_107388 v h) (hints_cons _ _ _ (der_59715 v h) (hints_cons _ _ _ (der_107846 v h) (hints_cons _ _ _ (der_49969 v h) (hints_cons _ _ _ (der_76665 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_44574 v h) (hints_cons _ _ _ (der_107287 v h) (hints_cons _ _ _ (der_54218 v h) (hints_cons _ _ _ (der_108035 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_60437 v h) (hints_cons _ _ _ (der_108036 v h) (hints_cons _ _ _ (inp_8048 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (inp_8101 v h) (hints_cons _ _ _ (inp_8114 v h) (hints_cons _ _ _ (der_15768 v h) (hints_cons _ _ _ (der_67569 v h) (hints_cons _ _ _ (der_107400 v h) (hints_cons _ _ _ (der_15767 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (der_76340 v h) (hints_cons _ _ _ (der_53892 v h) (hints_cons _ _ _ (der_49843 v h) (hints_cons _ _ _ (der_105390 v h) (hints_cons _ _ _ (der_49731 v h) (hints_cons _ _ _ (der_76756 v h) (hints_cons _ _ _ (der_94328 v h) (hints_cons _ _ _ (der_49761 v h) (hints_cons _ _ _ (der_107377 v h) (hints_cons _ _ _ (der_32081 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108038 : CNF.NClause := [(146,true),(148,true),(137,true),(134,true),(133,true),(131,false),(141,true),(129,true),(84,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108038 :=
  CNF.rup_sound cl_108038 [cl_76564,cl_105154,cl_105775,cl_15770,cl_106128,cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_76759,cl_15784,cl_105770,cl_76725,cl_15781,cl_105797,cl_101685,cl_8021,cl_88579,cl_15658,cl_108033,cl_88561,cl_15787,cl_15625,cl_67563,cl_8056,cl_62286,cl_62171,cl_88575,cl_88464,cl_62965,cl_105330,cl_61659,cl_49882,cl_76779,cl_105769,cl_80918,cl_15644,cl_108036,cl_15789,cl_8048,cl_106776,cl_8105,cl_15629,cl_105380,cl_15778,cl_76601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_88579 v h) (hints_cons _ _ _ (der_15658 v h) (hints_cons _ _ _ (der_108033 v h) (hints_cons _ _ _ (der_88561 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15625 v h) (hints_cons _ _ _ (der_67563 v h) (hints_cons _ _ _ (inp_8056 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_15644 v h) (hints_cons _ _ _ (der_108036 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (inp_8048 v h) (hints_cons _ _ _ (der_106776 v h) (hints_cons _ _ _ (inp_8105 v h) (hints_cons _ _ _ (der_15629 v h) (hints_cons _ _ _ (der_105380 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_76601 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108039 : CNF.NClause := [(133,true),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108039 :=
  CNF.rup_sound cl_108039 [cl_108032,cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_76759,cl_105154,cl_15784,cl_105770,cl_76725,cl_15781,cl_105797,cl_15770,cl_106128,cl_101685,cl_8021,cl_62286,cl_62171,cl_88575,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_105769,cl_80918,cl_78004,cl_107341,cl_76564,cl_105330,cl_107574,cl_108034,cl_108037,cl_15625,cl_107223,cl_108038,cl_105073,cl_35634,cl_107502,cl_104970,cl_8047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108032 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_108034 v h) (hints_cons _ _ _ (der_108037 v h) (hints_cons _ _ _ (der_15625 v h) (hints_cons _ _ _ (der_107223 v h) (hints_cons _ _ _ (der_108038 v h) (hints_cons _ _ _ (der_105073 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (der_104970 v h) (hints_cons _ _ _ (inp_8047 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))
def cl_108040 : CNF.NClause := [(53,false),(134,true),(94,false),(133,false),(131,false),(127,true),(84,false),(114,false),(151,true),(15,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108040 :=
  CNF.rup_sound cl_108040 [cl_15775,cl_15773,cl_76725,cl_105797,cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_107246,cl_105769,cl_80918,cl_106128,cl_78004,cl_107341,cl_105154,cl_105458,cl_83925,cl_15784,cl_107245,cl_50033,cl_107276,cl_35634,cl_107240,cl_107846,cl_105419,cl_107502,cl_7941,cl_70013,cl_15790,cl_105777,cl_70711,cl_49761,cl_42498,cl_15782,cl_15789,cl_97864,cl_8050,cl_49838,cl_15643,cl_107375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_107240 v h) (hints_cons _ _ _ (der_107846 v h) (hints_cons _ _ _ (der_105419 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (inp_7941 v h) (hints_cons _ _ _ (der_70013 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_105777 v h) (hints_cons _ _ _ (der_70711 v h) (hints_cons _ _ _ (der_49761 v h) (hints_cons _ _ _ (der_42498 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_97864 v h) (hints_cons _ _ _ (inp_8050 v h) (hints_cons _ _ _ (der_49838 v h) (hints_cons _ _ _ (der_15643 v h) (hints_cons _ _ _ (der_107375 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))
def cl_108041 : CNF.NClause := [(150,true),(146,true),(134,true),(133,false),(131,false),(127,true),(138,true),(141,true),(129,true),(84,false),(151,true),(70,false),(75,false),(35,false),(85,false),(3,false),(80,false),(71,false),(152,true),(142,false),(39,false),(68,false)]
theorem der_108041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108041 :=
  CNF.rup_sound cl_108041 [cl_15773,cl_107246,cl_105769,cl_80918,cl_79629,cl_15617,cl_8050,cl_8114,cl_15782,cl_70711,cl_105787,cl_49768,cl_76895,cl_105451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (inp_8050 v h) (hints_cons _ _ _ (inp_8114 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_70711 v h) (hints_cons _ _ _ (der_105787 v h) (hints_cons _ _ _ (der_49768 v h) (hints_cons _ _ _ (der_76895 v h) (hints_cons _ _ _ (der_105451 v h) (by intro d hd; cases hd)))))))))))))))
def cl_108042 : CNF.NClause := [(94,false),(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108042 :=
  CNF.rup_sound cl_108042 [cl_108039,cl_15775,cl_108032,cl_88579,cl_88560,cl_107246,cl_107245,cl_50033,cl_107276,cl_76759,cl_105154,cl_15784,cl_105770,cl_76725,cl_15781,cl_105797,cl_15770,cl_106128,cl_101685,cl_8021,cl_61659,cl_62286,cl_62171,cl_88575,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_105769,cl_80918,cl_78004,cl_107341,cl_93676,cl_79495,cl_107574,cl_108040,cl_107287,cl_108041,cl_15791,cl_107390,cl_15620,cl_107502,cl_49814,cl_36500,cl_15794,cl_67558,cl_49725,cl_105801,cl_107382,cl_49837,cl_40664,cl_105796,cl_105447,cl_68243,cl_50040,cl_62276,cl_76763,cl_15782,cl_107536,cl_105381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_108039 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_108032 v h) (hints_cons _ _ _ (der_88579 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_108040 v h) (hints_cons _ _ _ (der_107287 v h) (hints_cons _ _ _ (der_108041 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_107390 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (der_49814 v h) (hints_cons _ _ _ (der_36500 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_67558 v h) (hints_cons _ _ _ (der_49725 v h) (hints_cons _ _ _ (der_105801 v h) (hints_cons _ _ _ (der_107382 v h) (hints_cons _ _ _ (der_49837 v h) (hints_cons _ _ _ (der_40664 v h) (hints_cons _ _ _ (der_105796 v h) (hints_cons _ _ _ (der_105447 v h) (hints_cons _ _ _ (der_68243 v h) (hints_cons _ _ _ (der_50040 v h) (hints_cons _ _ _ (der_62276 v h) (hints_cons _ _ _ (der_76763 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_107536 v h) (hints_cons _ _ _ (der_105381 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108043 : CNF.NClause := [(141,true),(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108043 :=
  CNF.rup_sound cl_108043 [cl_88560,cl_107246,cl_105769,cl_80918,cl_105775,cl_107341,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_62965,cl_106128,cl_105154,cl_15784,cl_107245,cl_101685,cl_108032,cl_108042,cl_76761,cl_105195,cl_107388,cl_15787,cl_105513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_108032 v h) (hints_cons _ _ _ (der_108042 v h) (hints_cons _ _ _ (der_76761 v h) (hints_cons _ _ _ (der_105195 v h) (hints_cons _ _ _ (der_107388 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_105513 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_108044 : CNF.NClause := [(148,true),(134,true),(127,false),(150,true),(133,true),(153,true),(145,true),(131,false),(84,false),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108044 :=
  CNF.rup_sound cl_108044 [cl_15770,cl_106128,cl_88560,cl_62286,cl_62171,cl_88575,cl_88464,cl_105775,cl_62965,cl_105154,cl_15784,cl_107246,cl_107245,cl_42866,cl_15773,cl_105808,cl_105330,cl_76725,cl_15781,cl_105797,cl_61659,cl_49882,cl_76779,cl_76759,cl_105770,cl_105458,cl_105769,cl_80918,cl_15625,cl_67563,cl_105275,cl_8051,cl_63071,cl_105073,cl_15643,cl_35634,cl_15789,cl_106776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_42866 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_105808 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_15625 v h) (hints_cons _ _ _ (der_67563 v h) (hints_cons _ _ _ (der_105275 v h) (hints_cons _ _ _ (inp_8051 v h) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_105073 v h) (hints_cons _ _ _ (der_15643 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_106776 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))
def cl_108045 : CNF.NClause := [(129,true),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108045 :=
  CNF.rup_sound cl_108045 [cl_76725,cl_15781,cl_105797,cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_107246,cl_105769,cl_80918,cl_106128,cl_78004,cl_107341,cl_76759,cl_105154,cl_15784,cl_105770,cl_105458,cl_93676,cl_83925,cl_107245,cl_50033,cl_107276,cl_42866,cl_49841,cl_79495,cl_79629,cl_108043,cl_15783,cl_79619,cl_107412,cl_107413,cl_105600,cl_37352,cl_15787,cl_15794,cl_15773,cl_15775,cl_15620,cl_105808,cl_105330,cl_8018,cl_107574,cl_108044,cl_15790,cl_80957,cl_107388,cl_52763,cl_107846,cl_70013,cl_54642,cl_35634,cl_107287,cl_39659,cl_105473,cl_50718,cl_49761,cl_105787,cl_105387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_42866 v h) (hints_cons _ _ _ (der_49841 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_108043 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_79619 v h) (hints_cons _ _ _ (der_107412 v h) (hints_cons _ _ _ (der_107413 v h) (hints_cons _ _ _ (der_105600 v h) (hints_cons _ _ _ (der_37352 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_105808 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (inp_8018 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_108044 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_80957 v h) (hints_cons _ _ _ (der_107388 v h) (hints_cons _ _ _ (der_52763 v h) (hints_cons _ _ _ (der_107846 v h) (hints_cons _ _ _ (der_70013 v h) (hints_cons _ _ _ (der_54642 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_107287 v h) (hints_cons _ _ _ (der_39659 v h) (hints_cons _ _ _ (der_105473 v h) (hints_cons _ _ _ (der_50718 v h) (hints_cons _ _ _ (der_49761 v h) (hints_cons _ _ _ (der_105787 v h) (hints_cons _ _ _ (der_105387 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108046 : CNF.NClause := [(141,false),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108046 :=
  CNF.rup_sound cl_108046 [cl_79629,cl_62286,cl_61659,cl_15781,cl_105154,cl_15784,cl_108045,cl_15771,cl_61846,cl_42523,cl_76721,cl_88560,cl_62171,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_44574,cl_107306,cl_76793,cl_79690,cl_49882,cl_76779,cl_107246,cl_105769,cl_80918,cl_106128,cl_78004,cl_107341,cl_76759,cl_105770,cl_105458,cl_83925,cl_107245,cl_50033,cl_107276,cl_42866,cl_49841,cl_76564,cl_79619,cl_106125,cl_107412,cl_105600,cl_104684,cl_107776,cl_15779,cl_15787,cl_15773,cl_105419,cl_105808,cl_70711,cl_49761,cl_105330,cl_15782,cl_15789,cl_107574,cl_8084,cl_15649,cl_15640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_108045 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_61846 v h) (hints_cons _ _ _ (der_42523 v h) (hints_cons _ _ _ (der_76721 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_44574 v h) (hints_cons _ _ _ (der_107306 v h) (hints_cons _ _ _ (der_76793 v h) (hints_cons _ _ _ (der_79690 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_42866 v h) (hints_cons _ _ _ (der_49841 v h) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_79619 v h) (hints_cons _ _ _ (der_106125 v h) (hints_cons _ _ _ (der_107412 v h) (hints_cons _ _ _ (der_105600 v h) (hints_cons _ _ _ (der_104684 v h) (hints_cons _ _ _ (der_107776 v h) (hints_cons _ _ _ (der_15779 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_105419 v h) (hints_cons _ _ _ (der_105808 v h) (hints_cons _ _ _ (der_70711 v h) (hints_cons _ _ _ (der_49761 v h) (hints_cons _ _ _ (der_105330 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_15789 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (inp_8084 v h) (hints_cons _ _ _ (der_15649 v h) (hints_cons _ _ _ (der_15640 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108047 : CNF.NClause := [(94,false),(140,true),(136,true),(131,false),(141,true),(109,false),(123,false),(116,false),(129,false),(84,false),(114,false),(151,true),(144,true),(139,false),(118,false),(75,false),(35,false),(85,false),(71,false),(152,true),(142,false),(96,false),(39,false),(128,false)]
theorem der_108047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108047 :=
  CNF.rup_sound cl_108047 [cl_15781,cl_107306,cl_76661,cl_15771,cl_49882,cl_105458,cl_93676,cl_83925,cl_15784,cl_88560,cl_107246,cl_105769,cl_80918,cl_79495,cl_62171,cl_62286,cl_15770,cl_107574,cl_107673,cl_107502,cl_50022,cl_15617,cl_59715,cl_8009,cl_15790,cl_8056,cl_106470,cl_107282,cl_107500,cl_49896,cl_47827,cl_106324,cl_107287,cl_15629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_107306 v h) (hints_cons _ _ _ (der_76661 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_107673 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_59715 v h) (hints_cons _ _ _ (inp_8009 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (inp_8056 v h) (hints_cons _ _ _ (der_106470 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (der_107500 v h) (hints_cons _ _ _ (der_49896 v h) (hints_cons _ _ _ (der_47827 v h) (hints_cons _ _ _ (der_106324 v h) (hints_cons _ _ _ (der_107287 v h) (hints_cons _ _ _ (der_15629 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))
def cl_108048 : CNF.NClause := [(131,false),(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108048 :=
  CNF.rup_sound cl_108048 [cl_15770,cl_106128,cl_108046,cl_101685,cl_79629,cl_62286,cl_61659,cl_15781,cl_105154,cl_15784,cl_108045,cl_15771,cl_61846,cl_42523,cl_76721,cl_88560,cl_62171,cl_88575,cl_88464,cl_105775,cl_62965,cl_44574,cl_107306,cl_76793,cl_79690,cl_76725,cl_105797,cl_76779,cl_107246,cl_105769,cl_80918,cl_107341,cl_105458,cl_83925,cl_107245,cl_50033,cl_107276,cl_76564,cl_15773,cl_88579,cl_105419,cl_107776,cl_70711,cl_15782,cl_108047,cl_76761,cl_105195,cl_107388,cl_15787,cl_105513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_108046 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_108045 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_61846 v h) (hints_cons _ _ _ (der_42523 v h) (hints_cons _ _ _ (der_76721 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_44574 v h) (hints_cons _ _ _ (der_107306 v h) (hints_cons _ _ _ (der_76793 v h) (hints_cons _ _ _ (der_79690 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_88579 v h) (hints_cons _ _ _ (der_105419 v h) (hints_cons _ _ _ (der_107776 v h) (hints_cons _ _ _ (der_70711 v h) (hints_cons _ _ _ (der_15782 v h) (hints_cons _ _ _ (der_108047 v h) (hints_cons _ _ _ (der_76761 v h) (hints_cons _ _ _ (der_105195 v h) (hints_cons _ _ _ (der_107388 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_105513 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108049 : CNF.NClause := [(94,true),(127,true),(138,true),(111,false),(129,false),(84,false),(151,true),(139,false),(75,false),(35,false),(85,false),(80,false),(142,false),(39,false),(128,false)]
theorem der_108049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108049 :=
  CNF.rup_sound cl_108049 [cl_61659,cl_15781,cl_105458,cl_88560,cl_107246,cl_107245,cl_105769,cl_105195,cl_76677,cl_15787,cl_107223,cl_8110,cl_105267,cl_88580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_105195 v h) (hints_cons _ _ _ (der_76677 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_107223 v h) (hints_cons _ _ _ (inp_8110 v h) (hints_cons _ _ _ (der_105267 v h) (hints_cons _ _ _ (der_88580 v h) (by intro d hd; cases hd)))))))))))))))
def cl_108050 : CNF.NClause := [(84,false),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108050 :=
  CNF.rup_sound cl_108050 [cl_76725,cl_15781,cl_105797,cl_61659,cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_107246,cl_105769,cl_80918,cl_107341,cl_106128,cl_76759,cl_105154,cl_15784,cl_105770,cl_105458,cl_93676,cl_83925,cl_107245,cl_50033,cl_107276,cl_76564,cl_79495,cl_79629,cl_108045,cl_15771,cl_107306,cl_61846,cl_79690,cl_76661,cl_76793,cl_44574,cl_76721,cl_42523,cl_108046,cl_101685,cl_8021,cl_108048,cl_108049,cl_107574,cl_107673,cl_107502,cl_50022,cl_15617,cl_105799,cl_59715,cl_15778,cl_15790,cl_8078,cl_107296,cl_15649,cl_64116,cl_107501,cl_7945,cl_106470,cl_8072,cl_15630,cl_106324,cl_105073,cl_76792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_105458 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_76564 v h) (hints_cons _ _ _ (der_79495 v h) (hints_cons _ _ _ (der_79629 v h) (hints_cons _ _ _ (der_108045 v h) (hints_cons _ _ _ (der_15771 v h) (hints_cons _ _ _ (der_107306 v h) (hints_cons _ _ _ (der_61846 v h) (hints_cons _ _ _ (der_79690 v h) (hints_cons _ _ _ (der_76661 v h) (hints_cons _ _ _ (der_76793 v h) (hints_cons _ _ _ (der_44574 v h) (hints_cons _ _ _ (der_76721 v h) (hints_cons _ _ _ (der_42523 v h) (hints_cons _ _ _ (der_108046 v h) (hints_cons _ _ _ (der_101685 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_108048 v h) (hints_cons _ _ _ (der_108049 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_107673 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_105799 v h) (hints_cons _ _ _ (der_59715 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (inp_8078 v h) (hints_cons _ _ _ (der_107296 v h) (hints_cons _ _ _ (der_15649 v h) (hints_cons _ _ _ (der_64116 v h) (hints_cons _ _ _ (der_107501 v h) (hints_cons _ _ _ (inp_7945 v h) (hints_cons _ _ _ (der_106470 v h) (hints_cons _ _ _ (inp_8072 v h) (hints_cons _ _ _ (der_15630 v h) (hints_cons _ _ _ (der_106324 v h) (hints_cons _ _ _ (der_105073 v h) (hints_cons _ _ _ (der_76792 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108051 : CNF.NClause := [(136,true),(134,true),(94,false),(141,true),(138,true),(131,false),(126,true),(140,true),(148,true),(137,true),(151,true),(144,true),(81,false),(118,false),(70,false),(75,false),(85,false),(3,false),(80,false),(71,false),(130,true),(152,true),(142,false),(39,false),(128,false)]
theorem der_108051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108051 :=
  CNF.rup_sound cl_108051 [cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_62965,cl_49882,cl_93676,cl_83925,cl_107246,cl_107245,cl_15629,cl_15649,cl_63071,cl_105073,cl_8012,cl_35634,cl_47827,cl_15775,cl_107502,cl_104676,cl_15617,cl_103403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_93676 v h) (hints_cons _ _ _ (der_83925 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_15629 v h) (hints_cons _ _ _ (der_15649 v h) (hints_cons _ _ _ (der_63071 v h) (hints_cons _ _ _ (der_105073 v h) (hints_cons _ _ _ (inp_8012 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_47827 v h) (hints_cons _ _ _ (der_15775 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (der_104676 v h) (hints_cons _ _ _ (der_15617 v h) (hints_cons _ _ _ (der_103403 v h) (by intro d hd; cases hd)))))))))))))))))))))))))
def cl_108052 : CNF.NClause := [(94,false),(141,true),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108052 :=
  CNF.rup_sound cl_108052 [cl_42866,cl_108050,cl_105577,cl_15773,cl_105808,cl_103219,cl_75853,cl_65889,cl_66108,cl_61980,cl_76725,cl_15781,cl_105797,cl_61659,cl_88560,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_105775,cl_62965,cl_49882,cl_76779,cl_107246,cl_105769,cl_80918,cl_106128,cl_78004,cl_107341,cl_76759,cl_105154,cl_15784,cl_105770,cl_107245,cl_50033,cl_107276,cl_107574,cl_108051,cl_15778,cl_15648,cl_76601,cl_105799,cl_50022,cl_7941,cl_107473,cl_105381,cl_105380,cl_15791,cl_8114,cl_15617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42866 v h) (hints_cons _ _ _ (der_108050 v h) (hints_cons _ _ _ (der_105577 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_105808 v h) (hints_cons _ _ _ (der_103219 v h) (hints_cons _ _ _ (der_75853 v h) (hints_cons _ _ _ (der_65889 v h) (hints_cons _ _ _ (der_66108 v h) (hints_cons _ _ _ (der_61980 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_61659 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_49882 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_78004 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_108051 v h) (hints_cons _ _ _ (der_15778 v h) (hints_cons _ _ _ (der_15648 v h) (hints_cons _ _ _ (der_76601 v h) (hints_cons _ _ _ (der_105799 v h) (hints_cons _ _ _ (der_50022 v h) (hints_cons _ _ _ (inp_7941 v h) (hints_cons _ _ _ (der_107473 v h) (hints_cons _ _ _ (der_105381 v h) (hints_cons _ _ _ (der_105380 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (inp_8114 v h) (hints_cons _ _ _ (der_15617 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))))))))))
def cl_108053 : CNF.NClause := [(141,true),(114,false),(151,true),(139,false),(80,false),(71,false),(101,true),(34,false),(39,false),(128,false)]
theorem der_108053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_108053 :=
  CNF.rup_sound cl_108053 [cl_42866,cl_108050,cl_105577,cl_15773,cl_105808,cl_75853,cl_66108,cl_61980,cl_76725,cl_15781,cl_105797,cl_88560,cl_107246,cl_105769,cl_80918,cl_105775,cl_107341,cl_62286,cl_62171,cl_88575,cl_15770,cl_88464,cl_62965,cl_106128,cl_76759,cl_105154,cl_15784,cl_105770,cl_107245,cl_50033,cl_107276,cl_8021,cl_108052,cl_105195,cl_76677,cl_105533,cl_15787,cl_107223,cl_15794,cl_15662,cl_105248,cl_105523,cl_105787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42866 v h) (hints_cons _ _ _ (der_108050 v h) (hints_cons _ _ _ (der_105577 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_105808 v h) (hints_cons _ _ _ (der_75853 v h) (hints_cons _ _ _ (der_66108 v h) (hints_cons _ _ _ (der_61980 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_15781 v h) (hints_cons _ _ _ (der_105797 v h) (hints_cons _ _ _ (der_88560 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_105769 v h) (hints_cons _ _ _ (der_80918 v h) (hints_cons _ _ _ (der_105775 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_62286 v h) (hints_cons _ _ _ (der_62171 v h) (hints_cons _ _ _ (der_88575 v h) (hints_cons _ _ _ (der_15770 v h) (hints_cons _ _ _ (der_88464 v h) (hints_cons _ _ _ (der_62965 v h) (hints_cons _ _ _ (der_106128 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_105154 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_105770 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_50033 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (inp_8021 v h) (hints_cons _ _ _ (der_108052 v h) (hints_cons _ _ _ (der_105195 v h) (hints_cons _ _ _ (der_76677 v h) (hints_cons _ _ _ (der_105533 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_107223 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15662 v h) (hints_cons _ _ _ (der_105248 v h) (hints_cons _ _ _ (der_105523 v h) (hints_cons _ _ _ (der_105787 v h) (by intro d hd; cases hd))))))))))))))))))))))))))))))))))))))))))))
def chunk128 : List CNF.NClause := [cl_107217,cl_107219,cl_107220,cl_107221,cl_107222,cl_107223,cl_107224,cl_107226,cl_107227,cl_107228,cl_107229,cl_107230,cl_107231,cl_107232,cl_107233,cl_107234,cl_107235,cl_107236,cl_107239,cl_107240,cl_107241,cl_107242,cl_107243,cl_107244,cl_107245,cl_107246,cl_107247,cl_107248,cl_107249,cl_107250,cl_107251,cl_107252,cl_107253,cl_107254,cl_107255,cl_107256,cl_107257,cl_107259,cl_107260,cl_107261,cl_107262,cl_107264,cl_107266,cl_107269,cl_107270,cl_107271,cl_107272,cl_107273,cl_107275,cl_107276,cl_107277,cl_107278,cl_107279,cl_107281,cl_107282,cl_107283,cl_107284,cl_107285,cl_107286,cl_107287,cl_107288,cl_107289,cl_107290,cl_107291,cl_107292,cl_107293,cl_107294,cl_107296,cl_107297,cl_107298,cl_107299,cl_107300,cl_107301,cl_107302,cl_107303,cl_107304,cl_107305,cl_107306,cl_107307,cl_107308,cl_107309,cl_107310,cl_107311,cl_107312,cl_107314,cl_107315,cl_107317,cl_107318,cl_107320,cl_107321,cl_107322,cl_107323,cl_107325,cl_107326,cl_107327,cl_107328,cl_107330,cl_107331,cl_107332,cl_107333,cl_107334,cl_107335,cl_107336,cl_107337,cl_107338,cl_107340,cl_107341,cl_107342,cl_107344,cl_107345,cl_107348,cl_107355,cl_107358,cl_107360,cl_107361,cl_107365,cl_107366,cl_107367,cl_107369,cl_107370,cl_107371,cl_107372,cl_107373,cl_107374,cl_107375,cl_107376,cl_107377,cl_107378,cl_107379,cl_107380,cl_107381,cl_107382,cl_107383,cl_107384,cl_107385,cl_107386,cl_107387,cl_107388,cl_107389,cl_107390,cl_107391,cl_107392,cl_107393,cl_107394,cl_107395,cl_107397,cl_107398,cl_107399,cl_107400,cl_107403,cl_107404,cl_107405,cl_107406,cl_107407,cl_107409,cl_107410,cl_107411,cl_107412,cl_107413,cl_107414,cl_107415,cl_107416,cl_107417,cl_107418,cl_107419,cl_107421,cl_107422,cl_107424,cl_107425,cl_107426,cl_107427,cl_107428,cl_107429,cl_107432,cl_107433,cl_107435,cl_107436,cl_107442,cl_107445,cl_107446,cl_107447,cl_107448,cl_107450,cl_107451,cl_107455,cl_107456,cl_107458,cl_107459,cl_107460,cl_107461,cl_107462,cl_107463,cl_107464,cl_107466,cl_107467,cl_107468,cl_107469,cl_107470,cl_107471,cl_107472,cl_107473,cl_107475,cl_107476,cl_107477,cl_107478,cl_107479,cl_107480,cl_107481,cl_107483,cl_107484,cl_107485,cl_107486,cl_107487,cl_107489,cl_107490,cl_107491,cl_107494,cl_107495,cl_107496,cl_107498,cl_107499,cl_107500,cl_107501,cl_107502,cl_107504,cl_107508,cl_107510,cl_107511,cl_107512,cl_107513,cl_107514,cl_107515,cl_107519,cl_107520,cl_107521,cl_107522,cl_107523,cl_107524,cl_107525,cl_107526,cl_107527,cl_107528,cl_107529,cl_107531,cl_107532,cl_107533,cl_107534,cl_107536,cl_107537,cl_107538,cl_107539,cl_107540,cl_107542,cl_107544,cl_107545,cl_107547,cl_107548,cl_107549,cl_107550,cl_107551,cl_107552,cl_107553,cl_107554,cl_107555,cl_107556,cl_107557,cl_107558,cl_107559,cl_107560,cl_107561,cl_107562,cl_107566,cl_107567,cl_107568,cl_107569,cl_107570,cl_107571,cl_107573,cl_107574,cl_107576,cl_107581,cl_107582,cl_107583,cl_107584,cl_107585,cl_107591,cl_107592,cl_107593,cl_107594,cl_107595,cl_107596,cl_107597,cl_107598,cl_107599,cl_107600,cl_107601,cl_107602,cl_107604,cl_107606,cl_107608,cl_107609,cl_107610,cl_107611,cl_107614,cl_107615,cl_107617,cl_107618,cl_107619,cl_107620,cl_107621,cl_107622,cl_107623,cl_107624,cl_107625,cl_107626,cl_107627,cl_107628,cl_107629,cl_107631,cl_107632,cl_107633,cl_107634,cl_107637,cl_107639,cl_107641,cl_107642,cl_107643,cl_107644,cl_107645,cl_107649,cl_107650,cl_107653,cl_107655,cl_107657,cl_107658,cl_107659,cl_107667,cl_107669,cl_107673,cl_107674,cl_107675,cl_107677,cl_107679,cl_107680,cl_107681,cl_107682,cl_107686,cl_107688,cl_107689,cl_107690,cl_107691,cl_107692,cl_107697,cl_107699,cl_107700,cl_107701,cl_107702,cl_107704,cl_107705,cl_107706,cl_107707,cl_107710,cl_107711,cl_107712,cl_107714,cl_107715,cl_107716,cl_107717,cl_107718,cl_107719,cl_107720,cl_107721,cl_107722,cl_107723,cl_107724,cl_107725,cl_107726,cl_107727,cl_107729,cl_107730,cl_107731,cl_107732,cl_107733,cl_107735,cl_107740,cl_107741,cl_107742,cl_107744,cl_107745,cl_107746,cl_107747,cl_107748,cl_107750,cl_107753,cl_107754,cl_107756,cl_107758,cl_107763,cl_107765,cl_107766,cl_107767,cl_107769,cl_107771,cl_107772,cl_107776,cl_107780,cl_107786,cl_107788,cl_107790,cl_107791,cl_107792,cl_107794,cl_107795,cl_107796,cl_107800,cl_107802,cl_107804,cl_107811,cl_107813,cl_107817,cl_107818,cl_107820,cl_107823,cl_107838,cl_107840,cl_107843,cl_107844,cl_107846,cl_107847,cl_107849,cl_107851,cl_107852,cl_107853,cl_107854,cl_107856,cl_107859,cl_107861,cl_107862,cl_107865,cl_107867,cl_107870,cl_107871,cl_107874,cl_107877,cl_107878,cl_107883,cl_107887,cl_107889,cl_107891,cl_107892,cl_107896,cl_107899,cl_107910,cl_107913,cl_107916,cl_107917,cl_107922,cl_107929,cl_107930,cl_107932,cl_107942,cl_107948,cl_107952,cl_107956,cl_107983,cl_107990,cl_107992,cl_107997,cl_108022,cl_108023,cl_108024,cl_108025,cl_108026,cl_108027,cl_108028,cl_108029,cl_108030,cl_108031,cl_108032,cl_108033,cl_108034,cl_108035,cl_108036,cl_108037,cl_108038,cl_108039,cl_108040,cl_108041,cl_108042,cl_108043,cl_108044,cl_108045,cl_108046,cl_108047,cl_108048,cl_108049,cl_108050,cl_108051,cl_108052,cl_108053]
theorem chunk_sound128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk128, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_107217 v h) (hints_cons _ _ _ (der_107219 v h) (hints_cons _ _ _ (der_107220 v h) (hints_cons _ _ _ (der_107221 v h) (hints_cons _ _ _ (der_107222 v h) (hints_cons _ _ _ (der_107223 v h) (hints_cons _ _ _ (der_107224 v h) (hints_cons _ _ _ (der_107226 v h) (hints_cons _ _ _ (der_107227 v h) (hints_cons _ _ _ (der_107228 v h) (hints_cons _ _ _ (der_107229 v h) (hints_cons _ _ _ (der_107230 v h) (hints_cons _ _ _ (der_107231 v h) (hints_cons _ _ _ (der_107232 v h) (hints_cons _ _ _ (der_107233 v h) (hints_cons _ _ _ (der_107234 v h) (hints_cons _ _ _ (der_107235 v h) (hints_cons _ _ _ (der_107236 v h) (hints_cons _ _ _ (der_107239 v h) (hints_cons _ _ _ (der_107240 v h) (hints_cons _ _ _ (der_107241 v h) (hints_cons _ _ _ (der_107242 v h) (hints_cons _ _ _ (der_107243 v h) (hints_cons _ _ _ (der_107244 v h) (hints_cons _ _ _ (der_107245 v h) (hints_cons _ _ _ (der_107246 v h) (hints_cons _ _ _ (der_107247 v h) (hints_cons _ _ _ (der_107248 v h) (hints_cons _ _ _ (der_107249 v h) (hints_cons _ _ _ (der_107250 v h) (hints_cons _ _ _ (der_107251 v h) (hints_cons _ _ _ (der_107252 v h) (hints_cons _ _ _ (der_107253 v h) (hints_cons _ _ _ (der_107254 v h) (hints_cons _ _ _ (der_107255 v h) (hints_cons _ _ _ (der_107256 v h) (hints_cons _ _ _ (der_107257 v h) (hints_cons _ _ _ (der_107259 v h) (hints_cons _ _ _ (der_107260 v h) (hints_cons _ _ _ (der_107261 v h) (hints_cons _ _ _ (der_107262 v h) (hints_cons _ _ _ (der_107264 v h) (hints_cons _ _ _ (der_107266 v h) (hints_cons _ _ _ (der_107269 v h) (hints_cons _ _ _ (der_107270 v h) (hints_cons _ _ _ (der_107271 v h) (hints_cons _ _ _ (der_107272 v h) (hints_cons _ _ _ (der_107273 v h) (hints_cons _ _ _ (der_107275 v h) (hints_cons _ _ _ (der_107276 v h) (hints_cons _ _ _ (der_107277 v h) (hints_cons _ _ _ (der_107278 v h) (hints_cons _ _ _ (der_107279 v h) (hints_cons _ _ _ (der_107281 v h) (hints_cons _ _ _ (der_107282 v h) (hints_cons _ _ _ (der_107283 v h) (hints_cons _ _ _ (der_107284 v h) (hints_cons _ _ _ (der_107285 v h) (hints_cons _ _ _ (der_107286 v h) (hints_cons _ _ _ (der_107287 v h) (hints_cons _ _ _ (der_107288 v h) (hints_cons _ _ _ (der_107289 v h) (hints_cons _ _ _ (der_107290 v h) (hints_cons _ _ _ (der_107291 v h) (hints_cons _ _ _ (der_107292 v h) (hints_cons _ _ _ (der_107293 v h) (hints_cons _ _ _ (der_107294 v h) (hints_cons _ _ _ (der_107296 v h) (hints_cons _ _ _ (der_107297 v h) (hints_cons _ _ _ (der_107298 v h) (hints_cons _ _ _ (der_107299 v h) (hints_cons _ _ _ (der_107300 v h) (hints_cons _ _ _ (der_107301 v h) (hints_cons _ _ _ (der_107302 v h) (hints_cons _ _ _ (der_107303 v h) (hints_cons _ _ _ (der_107304 v h) (hints_cons _ _ _ (der_107305 v h) (hints_cons _ _ _ (der_107306 v h) (hints_cons _ _ _ (der_107307 v h) (hints_cons _ _ _ (der_107308 v h) (hints_cons _ _ _ (der_107309 v h) (hints_cons _ _ _ (der_107310 v h) (hints_cons _ _ _ (der_107311 v h) (hints_cons _ _ _ (der_107312 v h) (hints_cons _ _ _ (der_107314 v h) (hints_cons _ _ _ (der_107315 v h) (hints_cons _ _ _ (der_107317 v h) (hints_cons _ _ _ (der_107318 v h) (hints_cons _ _ _ (der_107320 v h) (hints_cons _ _ _ (der_107321 v h) (hints_cons _ _ _ (der_107322 v h) (hints_cons _ _ _ (der_107323 v h) (hints_cons _ _ _ (der_107325 v h) (hints_cons _ _ _ (der_107326 v h) (hints_cons _ _ _ (der_107327 v h) (hints_cons _ _ _ (der_107328 v h) (hints_cons _ _ _ (der_107330 v h) (hints_cons _ _ _ (der_107331 v h) (hints_cons _ _ _ (der_107332 v h) (hints_cons _ _ _ (der_107333 v h) (hints_cons _ _ _ (der_107334 v h) (hints_cons _ _ _ (der_107335 v h) (hints_cons _ _ _ (der_107336 v h) (hints_cons _ _ _ (der_107337 v h) (hints_cons _ _ _ (der_107338 v h) (hints_cons _ _ _ (der_107340 v h) (hints_cons _ _ _ (der_107341 v h) (hints_cons _ _ _ (der_107342 v h) (hints_cons _ _ _ (der_107344 v h) (hints_cons _ _ _ (der_107345 v h) (hints_cons _ _ _ (der_107348 v h) (hints_cons _ _ _ (der_107355 v h) (hints_cons _ _ _ (der_107358 v h) (hints_cons _ _ _ (der_107360 v h) (hints_cons _ _ _ (der_107361 v h) (hints_cons _ _ _ (der_107365 v h) (hints_cons _ _ _ (der_107366 v h) (hints_cons _ _ _ (der_107367 v h) (hints_cons _ _ _ (der_107369 v h) (hints_cons _ _ _ (der_107370 v h) (hints_cons _ _ _ (der_107371 v h) (hints_cons _ _ _ (der_107372 v h) (hints_cons _ _ _ (der_107373 v h) (hints_cons _ _ _ (der_107374 v h) (hints_cons _ _ _ (der_107375 v h) (hints_cons _ _ _ (der_107376 v h) (hints_cons _ _ _ (der_107377 v h) (hints_cons _ _ _ (der_107378 v h) (hints_cons _ _ _ (der_107379 v h) (hints_cons _ _ _ (der_107380 v h) (hints_cons _ _ _ (der_107381 v h) (hints_cons _ _ _ (der_107382 v h) (hints_cons _ _ _ (der_107383 v h) (hints_cons _ _ _ (der_107384 v h) (hints_cons _ _ _ (der_107385 v h) (hints_cons _ _ _ (der_107386 v h) (hints_cons _ _ _ (der_107387 v h) (hints_cons _ _ _ (der_107388 v h) (hints_cons _ _ _ (der_107389 v h) (hints_cons _ _ _ (der_107390 v h) (hints_cons _ _ _ (der_107391 v h) (hints_cons _ _ _ (der_107392 v h) (hints_cons _ _ _ (der_107393 v h) (hints_cons _ _ _ (der_107394 v h) (hints_cons _ _ _ (der_107395 v h) (hints_cons _ _ _ (der_107397 v h) (hints_cons _ _ _ (der_107398 v h) (hints_cons _ _ _ (der_107399 v h) (hints_cons _ _ _ (der_107400 v h) (hints_cons _ _ _ (der_107403 v h) (hints_cons _ _ _ (der_107404 v h) (hints_cons _ _ _ (der_107405 v h) (hints_cons _ _ _ (der_107406 v h) (hints_cons _ _ _ (der_107407 v h) (hints_cons _ _ _ (der_107409 v h) (hints_cons _ _ _ (der_107410 v h) (hints_cons _ _ _ (der_107411 v h) (hints_cons _ _ _ (der_107412 v h) (hints_cons _ _ _ (der_107413 v h) (hints_cons _ _ _ (der_107414 v h) (hints_cons _ _ _ (der_107415 v h) (hints_cons _ _ _ (der_107416 v h) (hints_cons _ _ _ (der_107417 v h) (hints_cons _ _ _ (der_107418 v h) (hints_cons _ _ _ (der_107419 v h) (hints_cons _ _ _ (der_107421 v h) (hints_cons _ _ _ (der_107422 v h) (hints_cons _ _ _ (der_107424 v h) (hints_cons _ _ _ (der_107425 v h) (hints_cons _ _ _ (der_107426 v h) (hints_cons _ _ _ (der_107427 v h) (hints_cons _ _ _ (der_107428 v h) (hints_cons _ _ _ (der_107429 v h) (hints_cons _ _ _ (der_107432 v h) (hints_cons _ _ _ (der_107433 v h) (hints_cons _ _ _ (der_107435 v h) (hints_cons _ _ _ (der_107436 v h) (hints_cons _ _ _ (der_107442 v h) (hints_cons _ _ _ (der_107445 v h) (hints_cons _ _ _ (der_107446 v h) (hints_cons _ _ _ (der_107447 v h) (hints_cons _ _ _ (der_107448 v h) (hints_cons _ _ _ (der_107450 v h) (hints_cons _ _ _ (der_107451 v h) (hints_cons _ _ _ (der_107455 v h) (hints_cons _ _ _ (der_107456 v h) (hints_cons _ _ _ (der_107458 v h) (hints_cons _ _ _ (der_107459 v h) (hints_cons _ _ _ (der_107460 v h) (hints_cons _ _ _ (der_107461 v h) (hints_cons _ _ _ (der_107462 v h) (hints_cons _ _ _ (der_107463 v h) (hints_cons _ _ _ (der_107464 v h) (hints_cons _ _ _ (der_107466 v h) (hints_cons _ _ _ (der_107467 v h) (hints_cons _ _ _ (der_107468 v h) (hints_cons _ _ _ (der_107469 v h) (hints_cons _ _ _ (der_107470 v h) (hints_cons _ _ _ (der_107471 v h) (hints_cons _ _ _ (der_107472 v h) (hints_cons _ _ _ (der_107473 v h) (hints_cons _ _ _ (der_107475 v h) (hints_cons _ _ _ (der_107476 v h) (hints_cons _ _ _ (der_107477 v h) (hints_cons _ _ _ (der_107478 v h) (hints_cons _ _ _ (der_107479 v h) (hints_cons _ _ _ (der_107480 v h) (hints_cons _ _ _ (der_107481 v h) (hints_cons _ _ _ (der_107483 v h) (hints_cons _ _ _ (der_107484 v h) (hints_cons _ _ _ (der_107485 v h) (hints_cons _ _ _ (der_107486 v h) (hints_cons _ _ _ (der_107487 v h) (hints_cons _ _ _ (der_107489 v h) (hints_cons _ _ _ (der_107490 v h) (hints_cons _ _ _ (der_107491 v h) (hints_cons _ _ _ (der_107494 v h) (hints_cons _ _ _ (der_107495 v h) (hints_cons _ _ _ (der_107496 v h) (hints_cons _ _ _ (der_107498 v h) (hints_cons _ _ _ (der_107499 v h) (hints_cons _ _ _ (der_107500 v h) (hints_cons _ _ _ (der_107501 v h) (hints_cons _ _ _ (der_107502 v h) (hints_cons _ _ _ (der_107504 v h) (hints_cons _ _ _ (der_107508 v h) (hints_cons _ _ _ (der_107510 v h) (hints_cons _ _ _ (der_107511 v h) (hints_cons _ _ _ (der_107512 v h) (hints_cons _ _ _ (der_107513 v h) (hints_cons _ _ _ (der_107514 v h) (hints_cons _ _ _ (der_107515 v h) (hints_cons _ _ _ (der_107519 v h) (hints_cons _ _ _ (der_107520 v h) (hints_cons _ _ _ (der_107521 v h) (hints_cons _ _ _ (der_107522 v h) (hints_cons _ _ _ (der_107523 v h) (hints_cons _ _ _ (der_107524 v h) (hints_cons _ _ _ (der_107525 v h) (hints_cons _ _ _ (der_107526 v h) (hints_cons _ _ _ (der_107527 v h) (hints_cons _ _ _ (der_107528 v h) (hints_cons _ _ _ (der_107529 v h) (hints_cons _ _ _ (der_107531 v h) (hints_cons _ _ _ (der_107532 v h) (hints_cons _ _ _ (der_107533 v h) (hints_cons _ _ _ (der_107534 v h) (hints_cons _ _ _ (der_107536 v h) (hints_cons _ _ _ (der_107537 v h) (hints_cons _ _ _ (der_107538 v h) (hints_cons _ _ _ (der_107539 v h) (hints_cons _ _ _ (der_107540 v h) (hints_cons _ _ _ (der_107542 v h) (hints_cons _ _ _ (der_107544 v h) (hints_cons _ _ _ (der_107545 v h) (hints_cons _ _ _ (der_107547 v h) (hints_cons _ _ _ (der_107548 v h) (hints_cons _ _ _ (der_107549 v h) (hints_cons _ _ _ (der_107550 v h) (hints_cons _ _ _ (der_107551 v h) (hints_cons _ _ _ (der_107552 v h) (hints_cons _ _ _ (der_107553 v h) (hints_cons _ _ _ (der_107554 v h) (hints_cons _ _ _ (der_107555 v h) (hints_cons _ _ _ (der_107556 v h) (hints_cons _ _ _ (der_107557 v h) (hints_cons _ _ _ (der_107558 v h) (hints_cons _ _ _ (der_107559 v h) (hints_cons _ _ _ (der_107560 v h) (hints_cons _ _ _ (der_107561 v h) (hints_cons _ _ _ (der_107562 v h) (hints_cons _ _ _ (der_107566 v h) (hints_cons _ _ _ (der_107567 v h) (hints_cons _ _ _ (der_107568 v h) (hints_cons _ _ _ (der_107569 v h) (hints_cons _ _ _ (der_107570 v h) (hints_cons _ _ _ (der_107571 v h) (hints_cons _ _ _ (der_107573 v h) (hints_cons _ _ _ (der_107574 v h) (hints_cons _ _ _ (der_107576 v h) (hints_cons _ _ _ (der_107581 v h) (hints_cons _ _ _ (der_107582 v h) (hints_cons _ _ _ (der_107583 v h) (hints_cons _ _ _ (der_107584 v h) (hints_cons _ _ _ (der_107585 v h) (hints_cons _ _ _ (der_107591 v h) (hints_cons _ _ _ (der_107592 v h) (hints_cons _ _ _ (der_107593 v h) (hints_cons _ _ _ (der_107594 v h) (hints_cons _ _ _ (der_107595 v h) (hints_cons _ _ _ (der_107596 v h) (hints_cons _ _ _ (der_107597 v h) (hints_cons _ _ _ (der_107598 v h) (hints_cons _ _ _ (der_107599 v h) (hints_cons _ _ _ (der_107600 v h) (hints_cons _ _ _ (der_107601 v h) (hints_cons _ _ _ (der_107602 v h) (hints_cons _ _ _ (der_107604 v h) (hints_cons _ _ _ (der_107606 v h) (hints_cons _ _ _ (der_107608 v h) (hints_cons _ _ _ (der_107609 v h) (hints_cons _ _ _ (der_107610 v h) (hints_cons _ _ _ (der_107611 v h) (hints_cons _ _ _ (der_107614 v h) (hints_cons _ _ _ (der_107615 v h) (hints_cons _ _ _ (der_107617 v h) (hints_cons _ _ _ (der_107618 v h) (hints_cons _ _ _ (der_107619 v h) (hints_cons _ _ _ (der_107620 v h) (hints_cons _ _ _ (der_107621 v h) (hints_cons _ _ _ (der_107622 v h) (hints_cons _ _ _ (der_107623 v h) (hints_cons _ _ _ (der_107624 v h) (hints_cons _ _ _ (der_107625 v h) (hints_cons _ _ _ (der_107626 v h) (hints_cons _ _ _ (der_107627 v h) (hints_cons _ _ _ (der_107628 v h) (hints_cons _ _ _ (der_107629 v h) (hints_cons _ _ _ (der_107631 v h) (hints_cons _ _ _ (der_107632 v h) (hints_cons _ _ _ (der_107633 v h) (hints_cons _ _ _ (der_107634 v h) (hints_cons _ _ _ (der_107637 v h) (hints_cons _ _ _ (der_107639 v h) (hints_cons _ _ _ (der_107641 v h) (hints_cons _ _ _ (der_107642 v h) (hints_cons _ _ _ (der_107643 v h) (hints_cons _ _ _ (der_107644 v h) (hints_cons _ _ _ (der_107645 v h) (hints_cons _ _ _ (der_107649 v h) (hints_cons _ _ _ (der_107650 v h) (hints_cons _ _ _ (der_107653 v h) (hints_cons _ _ _ (der_107655 v h) (hints_cons _ _ _ (der_107657 v h) (hints_cons _ _ _ (der_107658 v h) (hints_cons _ _ _ (der_107659 v h) (hints_cons _ _ _ (der_107667 v h) (hints_cons _ _ _ (der_107669 v h) (hints_cons _ _ _ (der_107673 v h) (hints_cons _ _ _ (der_107674 v h) (hints_cons _ _ _ (der_107675 v h) (hints_cons _ _ _ (der_107677 v h) (hints_cons _ _ _ (der_107679 v h) (hints_cons _ _ _ (der_107680 v h) (hints_cons _ _ _ (der_107681 v h) (hints_cons _ _ _ (der_107682 v h) (hints_cons _ _ _ (der_107686 v h) (hints_cons _ _ _ (der_107688 v h) (hints_cons _ _ _ (der_107689 v h) (hints_cons _ _ _ (der_107690 v h) (hints_cons _ _ _ (der_107691 v h) (hints_cons _ _ _ (der_107692 v h) (hints_cons _ _ _ (der_107697 v h) (hints_cons _ _ _ (der_107699 v h) (hints_cons _ _ _ (der_107700 v h) (hints_cons _ _ _ (der_107701 v h) (hints_cons _ _ _ (der_107702 v h) (hints_cons _ _ _ (der_107704 v h) (hints_cons _ _ _ (der_107705 v h) (hints_cons _ _ _ (der_107706 v h) (hints_cons _ _ _ (der_107707 v h) (hints_cons _ _ _ (der_107710 v h) (hints_cons _ _ _ (der_107711 v h) (hints_cons _ _ _ (der_107712 v h) (hints_cons _ _ _ (der_107714 v h) (hints_cons _ _ _ (der_107715 v h) (hints_cons _ _ _ (der_107716 v h) (hints_cons _ _ _ (der_107717 v h) (hints_cons _ _ _ (der_107718 v h) (hints_cons _ _ _ (der_107719 v h) (hints_cons _ _ _ (der_107720 v h) (hints_cons _ _ _ (der_107721 v h) (hints_cons _ _ _ (der_107722 v h) (hints_cons _ _ _ (der_107723 v h) (hints_cons _ _ _ (der_107724 v h) (hints_cons _ _ _ (der_107725 v h) (hints_cons _ _ _ (der_107726 v h) (hints_cons _ _ _ (der_107727 v h) (hints_cons _ _ _ (der_107729 v h) (hints_cons _ _ _ (der_107730 v h) (hints_cons _ _ _ (der_107731 v h) (hints_cons _ _ _ (der_107732 v h) (hints_cons _ _ _ (der_107733 v h) (hints_cons _ _ _ (der_107735 v h) (hints_cons _ _ _ (der_107740 v h) (hints_cons _ _ _ (der_107741 v h) (hints_cons _ _ _ (der_107742 v h) (hints_cons _ _ _ (der_107744 v h) (hints_cons _ _ _ (der_107745 v h) (hints_cons _ _ _ (der_107746 v h) (hints_cons _ _ _ (der_107747 v h) (hints_cons _ _ _ (der_107748 v h) (hints_cons _ _ _ (der_107750 v h) (hints_cons _ _ _ (der_107753 v h) (hints_cons _ _ _ (der_107754 v h) (hints_cons _ _ _ (der_107756 v h) (hints_cons _ _ _ (der_107758 v h) (hints_cons _ _ _ (der_107763 v h) (hints_cons _ _ _ (der_107765 v h) (hints_cons _ _ _ (der_107766 v h) (hints_cons _ _ _ (der_107767 v h) (hints_cons _ _ _ (der_107769 v h) (hints_cons _ _ _ (der_107771 v h) (hints_cons _ _ _ (der_107772 v h) (hints_cons _ _ _ (der_107776 v h) (hints_cons _ _ _ (der_107780 v h) (hints_cons _ _ _ (der_107786 v h) (hints_cons _ _ _ (der_107788 v h) (hints_cons _ _ _ (der_107790 v h) (hints_cons _ _ _ (der_107791 v h) (hints_cons _ _ _ (der_107792 v h) (hints_cons _ _ _ (der_107794 v h) (hints_cons _ _ _ (der_107795 v h) (hints_cons _ _ _ (der_107796 v h) (hints_cons _ _ _ (der_107800 v h) (hints_cons _ _ _ (der_107802 v h) (hints_cons _ _ _ (der_107804 v h) (hints_cons _ _ _ (der_107811 v h) (hints_cons _ _ _ (der_107813 v h) (hints_cons _ _ _ (der_107817 v h) (hints_cons _ _ _ (der_107818 v h) (hints_cons _ _ _ (der_107820 v h) (hints_cons _ _ _ (der_107823 v h) (hints_cons _ _ _ (der_107838 v h) (hints_cons _ _ _ (der_107840 v h) (hints_cons _ _ _ (der_107843 v h) (hints_cons _ _ _ (der_107844 v h) (hints_cons _ _ _ (der_107846 v h) (hints_cons _ _ _ (der_107847 v h) (hints_cons _ _ _ (der_107849 v h) (hints_cons _ _ _ (der_107851 v h) (hints_cons _ _ _ (der_107852 v h) (hints_cons _ _ _ (der_107853 v h) (hints_cons _ _ _ (der_107854 v h) (hints_cons _ _ _ (der_107856 v h) (hints_cons _ _ _ (der_107859 v h) (hints_cons _ _ _ (der_107861 v h) (hints_cons _ _ _ (der_107862 v h) (hints_cons _ _ _ (der_107865 v h) (hints_cons _ _ _ (der_107867 v h) (hints_cons _ _ _ (der_107870 v h) (hints_cons _ _ _ (der_107871 v h) (hints_cons _ _ _ (der_107874 v h) (hints_cons _ _ _ (der_107877 v h) (hints_cons _ _ _ (der_107878 v h) (hints_cons _ _ _ (der_107883 v h) (hints_cons _ _ _ (der_107887 v h) (hints_cons _ _ _ (der_107889 v h) (hints_cons _ _ _ (der_107891 v h) (hints_cons _ _ _ (der_107892 v h) (hints_cons _ _ _ (der_107896 v h) (hints_cons _ _ _ (der_107899 v h) (hints_cons _ _ _ (der_107910 v h) (hints_cons _ _ _ (der_107913 v h) (hints_cons _ _ _ (der_107916 v h) (hints_cons _ _ _ (der_107917 v h) (hints_cons _ _ _ (der_107922 v h) (hints_cons _ _ _ (der_107929 v h) (hints_cons _ _ _ (der_107930 v h) (hints_cons _ _ _ (der_107932 v h) (hints_cons _ _ _ (der_107942 v h) (hints_cons _ _ _ (der_107948 v h) (hints_cons _ _ _ (der_107952 v h) (hints_cons _ _ _ (der_107956 v h) (hints_cons _ _ _ (der_107983 v h) (hints_cons _ _ _ (der_107990 v h) (hints_cons _ _ _ (der_107992 v h) (hints_cons _ _ _ (der_107997 v h) (hints_cons _ _ _ (der_108022 v h) (hints_cons _ _ _ (der_108023 v h) (hints_cons _ _ _ (der_108024 v h) (hints_cons _ _ _ (der_108025 v h) (hints_cons _ _ _ (der_108026 v h) (hints_cons _ _ _ (der_108027 v h) (hints_cons _ _ _ (der_108028 v h) (hints_cons _ _ _ (der_108029 v h) (hints_cons _ _ _ (der_108030 v h) (hints_cons _ _ _ (der_108031 v h) (hints_cons _ _ _ (der_108032 v h) (hints_cons _ _ _ (der_108033 v h) (hints_cons _ _ _ (der_108034 v h) (hints_cons _ _ _ (der_108035 v h) (hints_cons _ _ _ (der_108036 v h) (hints_cons _ _ _ (der_108037 v h) (hints_cons _ _ _ (der_108038 v h) (hints_cons _ _ _ (der_108039 v h) (hints_cons _ _ _ (der_108040 v h) (hints_cons _ _ _ (der_108041 v h) (hints_cons _ _ _ (der_108042 v h) (hints_cons _ _ _ (der_108043 v h) (hints_cons _ _ _ (der_108044 v h) (hints_cons _ _ _ (der_108045 v h) (hints_cons _ _ _ (der_108046 v h) (hints_cons _ _ _ (der_108047 v h) (hints_cons _ _ _ (der_108048 v h) (hints_cons _ _ _ (der_108049 v h) (hints_cons _ _ _ (der_108050 v h) (hints_cons _ _ _ (der_108051 v h) (hints_cons _ _ _ (der_108052 v h) (hints_cons _ _ _ (der_108053 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix128 := prefix127 ++ chunk128
theorem prefix_sound128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix128, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound127 v h c hc
  · exact chunk_sound128 v h c hc
end Percolation.NReplay
