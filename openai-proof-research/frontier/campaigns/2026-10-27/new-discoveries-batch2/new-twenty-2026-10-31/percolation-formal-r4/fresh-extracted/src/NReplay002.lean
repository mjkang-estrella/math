import NReplay001
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_23159 : CNF.NClause := [(87,true),(3,false),(4,false),(1,false)]
theorem der_23159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23159 :=
  CNF.rup_sound cl_23159 [cl_15267,cl_15269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15267 v h) (hints_cons _ _ _ (der_15269 v h) (by intro d hd; cases hd)))
def cl_23162 : CNF.NClause := [(92,true),(20,false),(10,false),(15,false)]
theorem der_23162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23162 :=
  CNF.rup_sound cl_23162 [cl_15410,cl_15409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15410 v h) (hints_cons _ _ _ (der_15409 v h) (by intro d hd; cases hd)))
def cl_23163 : CNF.NClause := [(92,true),(20,false),(10,false),(5,true)]
theorem der_23163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23163 :=
  CNF.rup_sound cl_23163 [cl_15414,cl_23162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15414 v h) (hints_cons _ _ _ (der_23162 v h) (by intro d hd; cases hd)))
def cl_23164 : CNF.NClause := [(92,true),(5,true),(10,false),(15,false)]
theorem der_23164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23164 :=
  CNF.rup_sound cl_23164 [cl_15418,cl_23162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15418 v h) (hints_cons _ _ _ (der_23162 v h) (by intro d hd; cases hd)))
def cl_23165 : CNF.NClause := [(62,true),(28,false),(27,false),(29,false)]
theorem der_23165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23165 :=
  CNF.rup_sound cl_23165 [cl_15002,cl_15001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15002 v h) (hints_cons _ _ _ (der_15001 v h) (by intro d hd; cases hd)))
def cl_23166 : CNF.NClause := [(62,true),(27,false),(26,true),(29,false)]
theorem der_23166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23166 :=
  CNF.rup_sound cl_23166 [cl_15006,cl_23165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15006 v h) (hints_cons _ _ _ (der_23165 v h) (by intro d hd; cases hd)))
def cl_23167 : CNF.NClause := [(62,true),(28,false),(26,true),(27,false)]
theorem der_23167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23167 :=
  CNF.rup_sound cl_23167 [cl_15010,cl_23166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15010 v h) (hints_cons _ _ _ (der_23166 v h) (by intro d hd; cases hd)))
def cl_23168 : CNF.NClause := [(92,true),(10,false),(5,false),(15,false)]
theorem der_23168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23168 :=
  CNF.rup_sound cl_23168 [cl_15417,cl_15409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15417 v h) (hints_cons _ _ _ (der_15409 v h) (by intro d hd; cases hd)))
def cl_23169 : CNF.NClause := [(87,true),(3,false),(2,false),(4,false)]
theorem der_23169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23169 :=
  CNF.rup_sound cl_23169 [cl_15268,cl_23159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15268 v h) (hints_cons _ _ _ (der_23159 v h) (by intro d hd; cases hd)))
def cl_23170 : CNF.NClause := [(87,true),(4,false),(2,false),(1,true)]
theorem der_23170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23170 :=
  CNF.rup_sound cl_23170 [cl_15272,cl_23169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15272 v h) (hints_cons _ _ _ (der_23169 v h) (by intro d hd; cases hd)))
def cl_23171 : CNF.NClause := [(87,true),(2,false),(3,false),(1,true)]
theorem der_23171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23171 :=
  CNF.rup_sound cl_23171 [cl_15276,cl_23169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15276 v h) (hints_cons _ _ _ (der_23169 v h) (by intro d hd; cases hd)))
def cl_23172 : CNF.NClause := [(87,true),(3,false),(4,false),(2,true)]
theorem der_23172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23172 :=
  CNF.rup_sound cl_23172 [cl_15270,cl_15269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15270 v h) (hints_cons _ _ _ (der_15269 v h) (by intro d hd; cases hd)))
def cl_23173 : CNF.NClause := [(62,true),(28,false),(26,false),(29,false)]
theorem der_23173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23173 :=
  CNF.rup_sound cl_23173 [cl_15003,cl_15001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15003 v h) (hints_cons _ _ _ (der_15001 v h) (by intro d hd; cases hd)))
def cl_23174 : CNF.NClause := [(62,true),(29,false),(26,false),(27,true)]
theorem der_23174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23174 :=
  CNF.rup_sound cl_23174 [cl_15007,cl_23173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15007 v h) (hints_cons _ _ _ (der_23173 v h) (by intro d hd; cases hd)))
def cl_23175 : CNF.NClause := [(62,true),(28,false),(27,true),(26,false)]
theorem der_23175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23175 :=
  CNF.rup_sound cl_23175 [cl_15011,cl_23173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15011 v h) (hints_cons _ _ _ (der_23173 v h) (by intro d hd; cases hd)))
def cl_23176 : CNF.NClause := [(62,true),(28,false),(27,false),(26,false)]
theorem der_23176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23176 :=
  CNF.rup_sound cl_23176 [cl_15009,cl_15001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15009 v h) (hints_cons _ _ _ (der_15001 v h) (by intro d hd; cases hd)))
def cl_23178 : CNF.NClause := [(92,true),(20,false),(5,false),(10,false)]
theorem der_23178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23178 :=
  CNF.rup_sound cl_23178 [cl_15413,cl_15409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15413 v h) (hints_cons _ _ _ (der_15409 v h) (by intro d hd; cases hd)))
def cl_23179 : CNF.NClause := [(92,true),(5,false),(10,false),(20,true)]
theorem der_23179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23179 :=
  CNF.rup_sound cl_23179 [cl_15421,cl_23168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15421 v h) (hints_cons _ _ _ (der_23168 v h) (by intro d hd; cases hd)))
def cl_23180 : CNF.NClause := [(87,true),(1,false),(4,false),(2,false)]
theorem der_23180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23180 :=
  CNF.rup_sound cl_23180 [cl_15271,cl_23169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15271 v h) (hints_cons _ _ _ (der_23169 v h) (by intro d hd; cases hd)))
def cl_23181 : CNF.NClause := [(87,true),(1,false),(2,false),(3,true)]
theorem der_23181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23181 :=
  CNF.rup_sound cl_23181 [cl_15279,cl_23180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15279 v h) (hints_cons _ _ _ (der_23180 v h) (by intro d hd; cases hd)))
def cl_23182 : CNF.NClause := [(62,true),(26,false),(29,false),(27,false)]
theorem der_23182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23182 :=
  CNF.rup_sound cl_23182 [cl_15005,cl_15001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15005 v h) (hints_cons _ _ _ (der_15001 v h) (by intro d hd; cases hd)))
def cl_23183 : CNF.NClause := [(62,true),(28,true),(26,false),(27,false)]
theorem der_23183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23183 :=
  CNF.rup_sound cl_23183 [cl_15013,cl_23182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15013 v h) (hints_cons _ _ _ (der_23182 v h) (by intro d hd; cases hd)))
def cl_23184 : CNF.NClause := [(92,true),(20,false),(5,false),(15,false)]
theorem der_23184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23184 :=
  CNF.rup_sound cl_23184 [cl_15411,cl_15409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15411 v h) (hints_cons _ _ _ (der_15409 v h) (by intro d hd; cases hd)))
def cl_23185 : CNF.NClause := [(92,true),(20,false),(5,false),(15,true)]
theorem der_23185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23185 :=
  CNF.rup_sound cl_23185 [cl_15415,cl_23178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15415 v h) (hints_cons _ _ _ (der_23178 v h) (by intro d hd; cases hd)))
def cl_23186 : CNF.NClause := [(92,true),(20,true),(5,false),(15,false)]
theorem der_23186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23186 :=
  CNF.rup_sound cl_23186 [cl_15419,cl_23168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15419 v h) (hints_cons _ _ _ (der_23168 v h) (by intro d hd; cases hd)))
def cl_23187 : CNF.NClause := [(92,true),(20,false),(5,true),(15,false)]
theorem der_23187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23187 :=
  CNF.rup_sound cl_23187 [cl_15412,cl_23162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15412 v h) (hints_cons _ _ _ (der_23162 v h) (by intro d hd; cases hd)))
def cl_23188 : CNF.NClause := [(87,true),(1,false),(2,false),(3,false)]
theorem der_23188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23188 :=
  CNF.rup_sound cl_23188 [cl_15275,cl_23169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15275 v h) (hints_cons _ _ _ (der_23169 v h) (by intro d hd; cases hd)))
def cl_23189 : CNF.NClause := [(89,true),(27,false),(23,false),(16,true)]
theorem der_23189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23189 :=
  CNF.rup_sound cl_23189 [cl_16178,cl_16166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_16178 v h) (hints_cons _ _ _ (der_16166 v h) (by intro d hd; cases hd)))
def cl_23190 : CNF.NClause := [(64,true),(12,false),(22,false),(2,false)]
theorem der_23190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23190 :=
  CNF.rup_sound cl_23190 [cl_16142,cl_14712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_16142 v h) (hints_cons _ _ _ (der_14712 v h) (by intro d hd; cases hd)))
def cl_23192 : CNF.NClause := [(89,true),(16,false),(7,true),(23,false),(14,false)]
theorem der_23192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23192 :=
  CNF.rup_sound cl_23192 [cl_15330,cl_14722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15330 v h) (hints_cons _ _ _ (der_14722 v h) (by intro d hd; cases hd)))
def cl_23193 : CNF.NClause := [(89,true),(14,false),(23,false),(16,false),(27,true)]
theorem der_23193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23193 :=
  CNF.rup_sound cl_23193 [cl_15329,cl_23192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15329 v h) (hints_cons _ _ _ (der_23192 v h) (by intro d hd; cases hd)))
def cl_23194 : CNF.NClause := [(66,false),(16,true),(21,true),(6,true),(11,true)]
theorem der_23194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23194 :=
  CNF.rup_sound cl_23194 [cl_15142,cl_15141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15142 v h) (hints_cons _ _ _ (der_15141 v h) (by intro d hd; cases hd)))
def cl_23195 : CNF.NClause := [(77,false),(15,true),(17,true),(16,true),(18,true)]
theorem der_23195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23195 :=
  CNF.rup_sound cl_23195 [cl_15238,cl_15222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15238 v h) (hints_cons _ _ _ (der_15222 v h) (by intro d hd; cases hd)))
def cl_23196 : CNF.NClause := [(21,true),(6,true),(1,true),(66,false),(16,true)]
theorem der_23196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23196 :=
  CNF.rup_sound cl_23196 [cl_15138,cl_23194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15138 v h) (hints_cons _ _ _ (der_23194 v h) (by intro d hd; cases hd)))
def cl_23197 : CNF.NClause := [(65,true),(8,true),(3,false),(13,false),(18,false)]
theorem der_23197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23197 :=
  CNF.rup_sound cl_23197 [cl_15097,cl_15081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15097 v h) (hints_cons _ _ _ (der_15081 v h) (by intro d hd; cases hd)))
def cl_23198 : CNF.NClause := [(65,true),(8,true),(3,false),(18,false),(23,true)]
theorem der_23198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23198 :=
  CNF.rup_sound cl_23198 [cl_15101,cl_23197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15101 v h) (hints_cons _ _ _ (der_23197 v h) (by intro d hd; cases hd)))
def cl_23199 : CNF.NClause := [(65,true),(8,true),(3,false),(13,false),(23,true)]
theorem der_23199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23199 :=
  CNF.rup_sound cl_23199 [cl_15105,cl_23197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15105 v h) (hints_cons _ _ _ (der_23197 v h) (by intro d hd; cases hd)))
def cl_23200 : CNF.NClause := [(91,false),(12,true),(18,true),(6,true),(24,true)]
theorem der_23200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23200 :=
  CNF.rup_sound cl_23200 [cl_15408,cl_15392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15408 v h) (hints_cons _ _ _ (der_15392 v h) (by intro d hd; cases hd)))
def cl_23201 : CNF.NClause := [(91,true),(12,false),(6,false),(26,false),(18,true)]
theorem der_23201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23201 :=
  CNF.rup_sound cl_23201 [cl_15389,cl_15381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15389 v h) (hints_cons _ _ _ (der_15381 v h) (by intro d hd; cases hd)))
def cl_23202 : CNF.NClause := [(91,true),(24,false),(6,false),(12,false),(18,true)]
theorem der_23202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23202 :=
  CNF.rup_sound cl_23202 [cl_15397,cl_15381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15397 v h) (hints_cons _ _ _ (der_15381 v h) (by intro d hd; cases hd)))
def cl_23203 : CNF.NClause := [(91,true),(12,false),(18,true),(6,false),(26,true)]
theorem der_23203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23203 :=
  CNF.rup_sound cl_23203 [cl_15405,cl_23202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15405 v h) (hints_cons _ _ _ (der_23202 v h) (by intro d hd; cases hd)))
def cl_23204 : CNF.NClause := [(91,true),(24,false),(12,true),(18,true),(26,false)]
theorem der_23204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23204 :=
  CNF.rup_sound cl_23204 [cl_15383,cl_15384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15383 v h) (hints_cons _ _ _ (der_15384 v h) (by intro d hd; cases hd)))
def cl_23205 : CNF.NClause := [(91,true),(6,false),(12,true),(18,true),(26,false)]
theorem der_23205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23205 :=
  CNF.rup_sound cl_23205 [cl_15391,cl_23204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15391 v h) (hints_cons _ _ _ (der_23204 v h) (by intro d hd; cases hd)))
def cl_23206 : CNF.NClause := [(91,false),(24,true),(26,true),(12,true),(18,true)]
theorem der_23206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23206 :=
  CNF.rup_sound cl_23206 [cl_15407,cl_23200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15407 v h) (hints_cons _ _ _ (der_23200 v h) (by intro d hd; cases hd)))
def cl_23207 : CNF.NClause := [(65,true),(8,true),(13,false),(3,false),(23,false)]
theorem der_23207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23207 :=
  CNF.rup_sound cl_23207 [cl_15089,cl_15081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15089 v h) (hints_cons _ _ _ (der_15081 v h) (by intro d hd; cases hd)))
def cl_23208 : CNF.NClause := [(90,true),(28,false),(19,false),(22,false),(11,false)]
theorem der_23208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23208 :=
  CNF.rup_sound cl_23208 [cl_15346,cl_15345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15346 v h) (hints_cons _ _ _ (der_15345 v h) (by intro d hd; cases hd)))
def cl_23209 : CNF.NClause := [(90,true),(28,false),(8,true),(19,false),(11,false)]
theorem der_23209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23209 :=
  CNF.rup_sound cl_23209 [cl_15354,cl_23208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15354 v h) (hints_cons _ _ _ (der_23208 v h) (by intro d hd; cases hd)))
def cl_23210 : CNF.NClause := [(90,true),(8,true),(19,false),(11,false),(22,false)]
theorem der_23210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23210 :=
  CNF.rup_sound cl_23210 [cl_15362,cl_23209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15362 v h) (hints_cons _ _ _ (der_23209 v h) (by intro d hd; cases hd)))
def cl_23211 : CNF.NClause := [(90,true),(19,false),(11,false),(22,true),(28,true)]
theorem der_23211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23211 :=
  CNF.rup_sound cl_23211 [cl_15370,cl_15369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15370 v h) (hints_cons _ _ _ (der_15369 v h) (by intro d hd; cases hd)))
def cl_23212 : CNF.NClause := [(90,true),(8,false),(22,true),(19,false),(11,false)]
theorem der_23212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23212 :=
  CNF.rup_sound cl_23212 [cl_15353,cl_15369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15353 v h) (hints_cons _ _ _ (der_15369 v h) (by intro d hd; cases hd)))
def cl_23213 : CNF.NClause := [(63,false),(4,true),(24,true),(9,true),(14,true)]
theorem der_23213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23213 :=
  CNF.rup_sound cl_23213 [cl_15048,cl_15040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15048 v h) (hints_cons _ _ _ (der_15040 v h) (by intro d hd; cases hd)))
def cl_23214 : CNF.NClause := [(63,false),(14,true),(9,true),(19,true),(24,true)]
theorem der_23214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23214 :=
  CNF.rup_sound cl_23214 [cl_15047,cl_23213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15047 v h) (hints_cons _ _ _ (der_23213 v h) (by intro d hd; cases hd)))
def cl_23215 : CNF.NClause := [(89,true),(27,false),(7,false),(16,true),(14,true)]
theorem der_23215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23215 :=
  CNF.rup_sound cl_23215 [cl_15327,cl_16166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15327 v h) (hints_cons _ _ _ (der_16166 v h) (by intro d hd; cases hd)))
def cl_23216 : CNF.NClause := [(89,true),(7,false),(16,false),(23,false),(27,true)]
theorem der_23216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23216 :=
  CNF.rup_sound cl_23216 [cl_15331,cl_23193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15331 v h) (hints_cons _ _ _ (der_23193 v h) (by intro d hd; cases hd)))
def cl_23217 : CNF.NClause := [(89,true),(16,true),(7,false),(14,true),(23,false)]
theorem der_23217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23217 :=
  CNF.rup_sound cl_23217 [cl_15335,cl_16166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15335 v h) (hints_cons _ _ _ (der_16166 v h) (by intro d hd; cases hd)))
def cl_23218 : CNF.NClause := [(89,true),(23,true),(7,false),(16,false),(14,true)]
theorem der_23218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23218 :=
  CNF.rup_sound cl_23218 [cl_15339,cl_15323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15339 v h) (hints_cons _ _ _ (der_15323 v h) (by intro d hd; cases hd)))
def cl_23219 : CNF.NClause := [(89,true),(27,true),(7,true),(16,false),(23,false)]
theorem der_23219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23219 :=
  CNF.rup_sound cl_23219 [cl_15332,cl_23193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15332 v h) (hints_cons _ _ _ (der_23193 v h) (by intro d hd; cases hd)))
def cl_23220 : CNF.NClause := [(89,true),(27,false),(7,true),(23,false),(14,true)]
theorem der_23220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23220 :=
  CNF.rup_sound cl_23220 [cl_15316,cl_16166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15316 v h) (hints_cons _ _ _ (der_16166 v h) (by intro d hd; cases hd)))
def cl_23221 : CNF.NClause := [(89,true),(27,false),(7,false),(14,true),(23,false)]
theorem der_23221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23221 :=
  CNF.rup_sound cl_23221 [cl_15315,cl_16166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15315 v h) (hints_cons _ _ _ (der_16166 v h) (by intro d hd; cases hd)))
def cl_23222 : CNF.NClause := [(77,false),(15,true),(18,true),(16,true),(19,true)]
theorem der_23222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23222 :=
  CNF.rup_sound cl_23222 [cl_15234,cl_23195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15234 v h) (hints_cons _ _ _ (der_23195 v h) (by intro d hd; cases hd)))
def cl_23223 : CNF.NClause := [(77,true),(17,false),(16,false),(15,false),(18,true)]
theorem der_23223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23223 :=
  CNF.rup_sound cl_23223 [cl_15231,cl_15215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15231 v h) (hints_cons _ _ _ (der_15215 v h) (by intro d hd; cases hd)))
def cl_23224 : CNF.NClause := [(64,true),(12,false),(2,false),(7,true),(17,false)]
theorem der_23224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23224 :=
  CNF.rup_sound cl_23224 [cl_15065,cl_14712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15065 v h) (hints_cons _ _ _ (der_14712 v h) (by intro d hd; cases hd)))
def cl_23225 : CNF.NClause := [(64,true),(22,false),(12,false),(7,true),(17,false)]
theorem der_23225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23225 :=
  CNF.rup_sound cl_23225 [cl_15050,cl_14712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15050 v h) (hints_cons _ _ _ (der_14712 v h) (by intro d hd; cases hd)))
def cl_23226 : CNF.NClause := [(64,true),(22,true),(17,false),(7,true),(12,false)]
theorem der_23226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23226 :=
  CNF.rup_sound cl_23226 [cl_15066,cl_23224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15066 v h) (hints_cons _ _ _ (der_23224 v h) (by intro d hd; cases hd)))
def cl_23227 : CNF.NClause := [(77,true),(16,true),(17,false),(19,false),(18,true)]
theorem der_23227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23227 :=
  CNF.rup_sound cl_23227 [cl_15217,cl_15218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15217 v h) (hints_cons _ _ _ (der_15218 v h) (by intro d hd; cases hd)))
def cl_23228 : CNF.NClause := [(77,true),(18,false),(17,false),(15,false),(16,true)]
theorem der_23228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23228 :=
  CNF.rup_sound cl_23228 [cl_15225,cl_15209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15225 v h) (hints_cons _ _ _ (der_15209 v h) (by intro d hd; cases hd)))
def cl_23229 : CNF.NClause := [(77,true),(17,false),(15,false),(19,true),(18,true)]
theorem der_23229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23229 :=
  CNF.rup_sound cl_23229 [cl_15233,cl_23223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15233 v h) (hints_cons _ _ _ (der_23223 v h) (by intro d hd; cases hd)))
def cl_23230 : CNF.NClause := [(77,true),(17,false),(19,false),(15,false),(16,false)]
theorem der_23230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23230 :=
  CNF.rup_sound cl_23230 [cl_15207,cl_15215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15207 v h) (hints_cons _ _ _ (der_15215 v h) (by intro d hd; cases hd)))
def cl_23231 : CNF.NClause := [(64,true),(7,false),(2,false),(17,false),(12,false)]
theorem der_23231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23231 :=
  CNF.rup_sound cl_23231 [cl_15063,cl_14712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15063 v h) (hints_cons _ _ _ (der_14712 v h) (by intro d hd; cases hd)))
def cl_23232 : CNF.NClause := [(77,true),(17,false),(15,false),(16,false),(18,false)]
theorem der_23232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23232 :=
  CNF.rup_sound cl_23232 [cl_15223,cl_23230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15223 v h) (hints_cons _ _ _ (der_23230 v h) (by intro d hd; cases hd)))
def cl_23233 : CNF.NClause := [(65,true),(3,false),(18,false),(13,false),(23,false)]
theorem der_23233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23233 :=
  CNF.rup_sound cl_23233 [cl_15079,cl_15081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15079 v h) (hints_cons _ _ _ (der_15081 v h) (by intro d hd; cases hd)))
def cl_23234 : CNF.NClause := [(65,true),(13,false),(18,false),(8,true),(23,false)]
theorem der_23234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23234 :=
  CNF.rup_sound cl_23234 [cl_15082,cl_15081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15082 v h) (hints_cons _ _ _ (der_15081 v h) (by intro d hd; cases hd)))
def cl_23235 : CNF.NClause := [(65,true),(23,false),(3,true),(13,false),(8,true)]
theorem der_23235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23235 :=
  CNF.rup_sound cl_23235 [cl_15090,cl_23234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15090 v h) (hints_cons _ _ _ (der_23234 v h) (by intro d hd; cases hd)))
def cl_23236 : CNF.NClause := [(65,true),(23,true),(13,false),(8,true),(18,false)]
theorem der_23236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23236 :=
  CNF.rup_sound cl_23236 [cl_15098,cl_23199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15098 v h) (hints_cons _ _ _ (der_23199 v h) (by intro d hd; cases hd)))
def cl_23237 : CNF.NClause := [(72,true),(12,true),(13,false),(11,false),(10,false)]
theorem der_23237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23237 :=
  CNF.rup_sound cl_23237 [cl_15179,cl_15195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15179 v h) (hints_cons _ _ _ (der_15195 v h) (by intro d hd; cases hd)))
def cl_23238 : CNF.NClause := [(65,true),(23,true),(3,false),(13,false),(18,false)]
theorem der_23238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23238 :=
  CNF.rup_sound cl_23238 [cl_15095,cl_23199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15095 v h) (hints_cons _ _ _ (der_23199 v h) (by intro d hd; cases hd)))
def cl_23239 : CNF.NClause := [(65,true),(13,false),(8,false),(3,false),(23,false)]
theorem der_23239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23239 :=
  CNF.rup_sound cl_23239 [cl_15087,cl_23233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15087 v h) (hints_cons _ _ _ (der_23233 v h) (by intro d hd; cases hd)))
def cl_23240 : CNF.NClause := [(65,true),(18,true),(3,false),(23,true),(13,false)]
theorem der_23240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23240 :=
  CNF.rup_sound cl_23240 [cl_15103,cl_23199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15103 v h) (hints_cons _ _ _ (der_23199 v h) (by intro d hd; cases hd)))
def cl_23241 : CNF.NClause := [(71,true),(26,false),(13,false),(1,false),(20,false)]
theorem der_23241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23241 :=
  CNF.rup_sound cl_23241 [cl_16162,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_16162 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_23242 : CNF.NClause := [(72,true),(14,false),(10,false),(11,false),(13,false)]
theorem der_23242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23242 :=
  CNF.rup_sound cl_23242 [cl_15175,cl_23237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15175 v h) (hints_cons _ _ _ (der_23237 v h) (by intro d hd; cases hd)))
def cl_23243 : CNF.NClause := [(72,true),(14,true),(10,false),(11,false),(13,false)]
theorem der_23243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23243 :=
  CNF.rup_sound cl_23243 [cl_15191,cl_15195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15191 v h) (hints_cons _ _ _ (der_15195 v h) (by intro d hd; cases hd)))
def cl_23244 : CNF.NClause := [(63,false),(24,true),(4,true),(14,true),(19,true)]
theorem der_23244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23244 :=
  CNF.rup_sound cl_23244 [cl_15046,cl_23213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15046 v h) (hints_cons _ _ _ (der_23213 v h) (by intro d hd; cases hd)))
def cl_23245 : CNF.NClause := [(63,true),(24,false),(4,false),(9,false),(14,false)]
theorem der_23245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23245 :=
  CNF.rup_sound cl_23245 [cl_15017,cl_15025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15017 v h) (hints_cons _ _ _ (der_15025 v h) (by intro d hd; cases hd)))
def cl_23246 : CNF.NClause := [(88,true),(17,false),(13,false),(29,true),(21,true)]
theorem der_23246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23246 :=
  CNF.rup_sound cl_23246 [cl_15307,cl_15308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15307 v h) (hints_cons _ _ _ (der_15308 v h) (by intro d hd; cases hd)))
def cl_23247 : CNF.NClause := [(63,true),(24,false),(4,false),(9,false),(19,false)]
theorem der_23247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23247 :=
  CNF.rup_sound cl_23247 [cl_15021,cl_23245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15021 v h) (hints_cons _ _ _ (der_23245 v h) (by intro d hd; cases hd)))
def cl_23248 : CNF.NClause := [(63,true),(24,false),(4,false),(9,false),(19,true)]
theorem der_23248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23248 :=
  CNF.rup_sound cl_23248 [cl_15029,cl_15025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15029 v h) (hints_cons _ _ _ (der_15025 v h) (by intro d hd; cases hd)))
def cl_23249 : CNF.NClause := [(63,true),(4,false),(9,false),(14,true),(19,false)]
theorem der_23249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23249 :=
  CNF.rup_sound cl_23249 [cl_15037,cl_23247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15037 v h) (hints_cons _ _ _ (der_23247 v h) (by intro d hd; cases hd)))
def cl_23250 : CNF.NClause := [(63,true),(24,true),(9,false),(4,false),(14,true)]
theorem der_23250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23250 :=
  CNF.rup_sound cl_23250 [cl_15045,cl_23249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15045 v h) (hints_cons _ _ _ (der_23249 v h) (by intro d hd; cases hd)))
def cl_23251 : CNF.NClause := [(67,true),(20,false),(23,false),(21,true),(24,false)]
theorem der_23251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23251 :=
  CNF.rup_sound cl_23251 [cl_15149,cl_15145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15149 v h) (hints_cons _ _ _ (der_15145 v h) (by intro d hd; cases hd)))
def cl_23252 : CNF.NClause := [(67,true),(20,false),(22,false),(24,false),(21,true)]
theorem der_23252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23252 :=
  CNF.rup_sound cl_23252 [cl_15153,cl_15145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15153 v h) (hints_cons _ _ _ (der_15145 v h) (by intro d hd; cases hd)))
def cl_23253 : CNF.NClause := [(67,true),(20,false),(22,true),(21,true),(24,false)]
theorem der_23253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23253 :=
  CNF.rup_sound cl_23253 [cl_15157,cl_23251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15157 v h) (hints_cons _ _ _ (der_23251 v h) (by intro d hd; cases hd)))
def cl_23254 : CNF.NClause := [(67,true),(20,false),(23,false),(21,true),(22,false)]
theorem der_23254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23254 :=
  CNF.rup_sound cl_23254 [cl_15161,cl_15145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15161 v h) (hints_cons _ _ _ (der_15145 v h) (by intro d hd; cases hd)))
def cl_23255 : CNF.NClause := [(67,true),(20,false),(23,false),(22,true),(21,true)]
theorem der_23255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23255 :=
  CNF.rup_sound cl_23255 [cl_15165,cl_23251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15165 v h) (hints_cons _ _ _ (der_23251 v h) (by intro d hd; cases hd)))
def cl_23256 : CNF.NClause := [(67,true),(20,false),(22,false),(23,true),(21,true)]
theorem der_23256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23256 :=
  CNF.rup_sound cl_23256 [cl_15169,cl_23252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15169 v h) (hints_cons _ _ _ (der_23252 v h) (by intro d hd; cases hd)))
def cl_23257 : CNF.NClause := [(88,true),(29,false),(21,true),(17,true),(13,false)]
theorem der_23257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23257 :=
  CNF.rup_sound cl_23257 [cl_15295,cl_15296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15295 v h) (hints_cons _ _ _ (der_15296 v h) (by intro d hd; cases hd)))
def cl_23258 : CNF.NClause := [(88,true),(29,false),(17,true),(9,false),(21,true)]
theorem der_23258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23258 :=
  CNF.rup_sound cl_23258 [cl_15297,cl_23257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15297 v h) (hints_cons _ _ _ (der_23257 v h) (by intro d hd; cases hd)))
def cl_23259 : CNF.NClause := [(88,true),(21,true),(13,false),(17,false),(9,false)]
theorem der_23259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23259 :=
  CNF.rup_sound cl_23259 [cl_15291,cl_23246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15291 v h) (hints_cons _ _ _ (der_23246 v h) (by intro d hd; cases hd)))
def cl_23260 : CNF.NClause := [(88,true),(21,true),(17,false),(9,false),(29,false)]
theorem der_23260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23260 :=
  CNF.rup_sound cl_23260 [cl_15293,cl_23259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15293 v h) (hints_cons _ _ _ (der_23259 v h) (by intro d hd; cases hd)))
def cl_23261 : CNF.NClause := [(88,true),(21,true),(17,false),(13,false),(9,true)]
theorem der_23261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23261 :=
  CNF.rup_sound cl_23261 [cl_15292,cl_15308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15292 v h) (hints_cons _ _ _ (der_15308 v h) (by intro d hd; cases hd)))
def cl_23262 : CNF.NClause := [(73,true),(21,true),(4,false),(10,false),(28,false)]
theorem der_23262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23262 :=
  CNF.rup_sound cl_23262 [cl_16193,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_16193 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_23263 : CNF.NClause := [(66,true),(21,true),(1,false),(6,false),(11,false)]
theorem der_23263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23263 :=
  CNF.rup_sound cl_23263 [cl_15135,cl_15127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15135 v h) (hints_cons _ _ _ (der_15127 v h) (by intro d hd; cases hd)))
def cl_23264 : CNF.NClause := [(91,false),(12,true),(6,true),(24,true),(26,true)]
theorem der_23264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23264 :=
  CNF.rup_sound cl_23264 [cl_15404,cl_23206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15404 v h) (hints_cons _ _ _ (der_23206 v h) (by intro d hd; cases hd)))
def cl_23265 : CNF.NClause := [(91,false),(26,true),(18,true),(24,true),(6,true)]
theorem der_23265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23265 :=
  CNF.rup_sound cl_23265 [cl_15406,cl_23206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15406 v h) (hints_cons _ _ _ (der_23206 v h) (by intro d hd; cases hd)))
def cl_23267 : CNF.NClause := [(65,false),(23,true),(3,true),(13,true),(18,true)]
theorem der_23267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23267 :=
  CNF.rup_sound cl_23267 [cl_15110,cl_15108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15110 v h) (hints_cons _ _ _ (der_15108 v h) (by intro d hd; cases hd)))
def cl_23270 : CNF.NClause := [(77,false),(15,true),(17,true),(19,true),(18,true)]
theorem der_23270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23270 :=
  CNF.rup_sound cl_23270 [cl_15236,cl_23222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15236 v h) (hints_cons _ _ _ (der_23222 v h) (by intro d hd; cases hd)))
def cl_23271 : CNF.NClause := [(77,false),(16,true),(17,true),(19,true),(18,true)]
theorem der_23271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23271 :=
  CNF.rup_sound cl_23271 [cl_15237,cl_23222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15237 v h) (hints_cons _ _ _ (der_23222 v h) (by intro d hd; cases hd)))
def cl_23272 : CNF.NClause := [(72,false),(13,true),(10,true),(11,true),(12,true)]
theorem der_23272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23272 :=
  CNF.rup_sound cl_23272 [cl_15206,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15206 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_23274 : CNF.NClause := [(95,true),(43,false),(56,true),(33,false),(53,false)]
theorem der_23274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23274 :=
  CNF.rup_sound cl_23274 [cl_16140,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_16140 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_23275 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(9,false)]
theorem der_23275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23275 :=
  CNF.rup_sound cl_23275 [cl_15245,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15245 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23276 : CNF.NClause := [(82,true),(5,false),(6,false),(7,false),(9,true)]
theorem der_23276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23276 :=
  CNF.rup_sound cl_23276 [cl_15259,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15259 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23277 : CNF.NClause := [(65,false),(13,true),(3,true),(23,true),(8,true)]
theorem der_23277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23277 :=
  CNF.rup_sound cl_23277 [cl_15102,cl_23267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15102 v h) (hints_cons _ _ _ (der_23267 v h) (by intro d hd; cases hd)))
def cl_23278 : CNF.NClause := [(90,true),(8,true),(28,false),(11,false),(22,false)]
theorem der_23278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23278 :=
  CNF.rup_sound cl_23278 [cl_15350,cl_23210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15350 v h) (hints_cons _ _ _ (der_23210 v h) (by intro d hd; cases hd)))
def cl_23279 : CNF.NClause := [(90,true),(8,true),(28,false),(11,false),(19,true)]
theorem der_23279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23279 :=
  CNF.rup_sound cl_23279 [cl_15358,cl_23278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15358 v h) (hints_cons _ _ _ (der_23278 v h) (by intro d hd; cases hd)))
def cl_23280 : CNF.NClause := [(66,true),(1,false),(6,true),(16,false),(21,false)]
theorem der_23280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23280 :=
  CNF.rup_sound cl_23280 [cl_15117,cl_15113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15117 v h) (hints_cons _ _ _ (der_15113 v h) (by intro d hd; cases hd)))
def cl_23281 : CNF.NClause := [(66,true),(11,false),(1,false),(21,false),(6,true)]
theorem der_23281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23281 :=
  CNF.rup_sound cl_23281 [cl_15121,cl_23280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15121 v h) (hints_cons _ _ _ (der_23280 v h) (by intro d hd; cases hd)))
def cl_23282 : CNF.NClause := [(66,true),(1,false),(6,true),(11,true),(21,false)]
theorem der_23282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23282 :=
  CNF.rup_sound cl_23282 [cl_15125,cl_23280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15125 v h) (hints_cons _ _ _ (der_23280 v h) (by intro d hd; cases hd)))
def cl_23283 : CNF.NClause := [(66,true),(1,false),(11,false),(16,false),(21,true)]
theorem der_23283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23283 :=
  CNF.rup_sound cl_23283 [cl_15129,cl_15127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15129 v h) (hints_cons _ _ _ (der_15127 v h) (by intro d hd; cases hd)))
def cl_23284 : CNF.NClause := [(66,true),(11,true),(1,false),(6,true),(16,false)]
theorem der_23284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23284 :=
  CNF.rup_sound cl_23284 [cl_15133,cl_23280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15133 v h) (hints_cons _ _ _ (der_23280 v h) (by intro d hd; cases hd)))
def cl_23285 : CNF.NClause := [(66,true),(21,true),(1,false),(11,false),(16,true)]
theorem der_23285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23285 :=
  CNF.rup_sound cl_23285 [cl_15137,cl_23263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15137 v h) (hints_cons _ _ _ (der_23263 v h) (by intro d hd; cases hd)))
def cl_23286 : CNF.NClause := [(82,true),(5,false),(7,false),(8,false),(9,false)]
theorem der_23286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23286 :=
  CNF.rup_sound cl_23286 [cl_15240,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15240 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23287 : CNF.NClause := [(82,true),(8,false),(7,true),(5,false),(9,false)]
theorem der_23287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23287 :=
  CNF.rup_sound cl_23287 [cl_15243,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15243 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23288 : CNF.NClause := [(82,true),(5,false),(7,false),(8,true),(9,false)]
theorem der_23288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23288 :=
  CNF.rup_sound cl_23288 [cl_15247,cl_23275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15247 v h) (hints_cons _ _ _ (der_23275 v h) (by intro d hd; cases hd)))
def cl_23289 : CNF.NClause := [(82,true),(6,true),(7,true),(5,false),(9,false)]
theorem der_23289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23289 :=
  CNF.rup_sound cl_23289 [cl_15251,cl_23287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15251 v h) (hints_cons _ _ _ (der_23287 v h) (by intro d hd; cases hd)))
def cl_23290 : CNF.NClause := [(82,true),(5,false),(7,false),(8,false),(9,true)]
theorem der_23290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23290 :=
  CNF.rup_sound cl_23290 [cl_15254,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15254 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23291 : CNF.NClause := [(82,true),(9,true),(5,false),(7,true),(8,false)]
theorem der_23291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23291 :=
  CNF.rup_sound cl_23291 [cl_15257,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15257 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23292 : CNF.NClause := [(82,true),(5,false),(7,false),(8,true),(9,true)]
theorem der_23292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23292 :=
  CNF.rup_sound cl_23292 [cl_15261,cl_23276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15261 v h) (hints_cons _ _ _ (der_23276 v h) (by intro d hd; cases hd)))
def cl_23293 : CNF.NClause := [(91,true),(24,false),(6,true),(18,true),(26,false)]
theorem der_23293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23293 :=
  CNF.rup_sound cl_23293 [cl_15382,cl_15384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15382 v h) (hints_cons _ _ _ (der_15384 v h) (by intro d hd; cases hd)))
def cl_23294 : CNF.NClause := [(91,true),(12,false),(6,true),(26,false),(18,false)]
theorem der_23294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23294 :=
  CNF.rup_sound cl_23294 [cl_15386,cl_15378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15386 v h) (hints_cons _ _ _ (der_15378 v h) (by intro d hd; cases hd)))
def cl_23295 : CNF.NClause := [(91,true),(12,false),(26,false),(6,true),(24,true)]
theorem der_23295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23295 :=
  CNF.rup_sound cl_23295 [cl_15390,cl_23294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15390 v h) (hints_cons _ _ _ (der_23294 v h) (by intro d hd; cases hd)))
def cl_23296 : CNF.NClause := [(91,true),(12,false),(6,true),(24,false),(18,false)]
theorem der_23296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23296 :=
  CNF.rup_sound cl_23296 [cl_15394,cl_15378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15394 v h) (hints_cons _ _ _ (der_15378 v h) (by intro d hd; cases hd)))
def cl_23297 : CNF.NClause := [(91,true),(26,true),(12,false),(18,true),(24,false)]
theorem der_23297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23297 :=
  CNF.rup_sound cl_23297 [cl_15398,cl_23202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15398 v h) (hints_cons _ _ _ (der_23202 v h) (by intro d hd; cases hd)))
def cl_23298 : CNF.NClause := [(91,true),(12,false),(24,true),(6,true),(18,false)]
theorem der_23298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23298 :=
  CNF.rup_sound cl_23298 [cl_15402,cl_23294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15402 v h) (hints_cons _ _ _ (der_23294 v h) (by intro d hd; cases hd)))
def cl_23299 : CNF.NClause := [(66,true),(16,false),(11,false),(6,true),(21,false)]
theorem der_23299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23299 :=
  CNF.rup_sound cl_23299 [cl_15114,cl_23280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15114 v h) (hints_cons _ _ _ (der_23280 v h) (by intro d hd; cases hd)))
def cl_23300 : CNF.NClause := [(66,true),(16,true),(11,false),(6,true),(21,false)]
theorem der_23300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23300 :=
  CNF.rup_sound cl_23300 [cl_15122,cl_23281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15122 v h) (hints_cons _ _ _ (der_23281 v h) (by intro d hd; cases hd)))
def cl_23301 : CNF.NClause := [(66,true),(6,true),(11,false),(16,false),(21,true)]
theorem der_23301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23301 :=
  CNF.rup_sound cl_23301 [cl_15130,cl_23283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15130 v h) (hints_cons _ _ _ (der_23283 v h) (by intro d hd; cases hd)))
def cl_23302 : CNF.NClause := [(82,true),(6,true),(7,false),(8,false),(9,false)]
theorem der_23302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23302 :=
  CNF.rup_sound cl_23302 [cl_15241,cl_23286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15241 v h) (hints_cons _ _ _ (der_23286 v h) (by intro d hd; cases hd)))
def cl_23303 : CNF.NClause := [(82,true),(6,true),(7,false),(8,true),(9,false)]
theorem der_23303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23303 :=
  CNF.rup_sound cl_23303 [cl_15248,cl_23288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15248 v h) (hints_cons _ _ _ (der_23288 v h) (by intro d hd; cases hd)))
def cl_23304 : CNF.NClause := [(82,true),(6,true),(7,false),(8,false),(9,true)]
theorem der_23304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23304 :=
  CNF.rup_sound cl_23304 [cl_15255,cl_23290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15255 v h) (hints_cons _ _ _ (der_23290 v h) (by intro d hd; cases hd)))
def cl_23305 : CNF.NClause := [(91,true),(24,false),(6,true),(12,true),(26,false)]
theorem der_23305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23305 :=
  CNF.rup_sound cl_23305 [cl_15380,cl_15384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15380 v h) (hints_cons _ _ _ (der_15384 v h) (by intro d hd; cases hd)))
def cl_23306 : CNF.NClause := [(91,true),(24,false),(6,true),(12,true),(18,false)]
theorem der_23306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23306 :=
  CNF.rup_sound cl_23306 [cl_15396,cl_23305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15396 v h) (hints_cons _ _ _ (der_23305 v h) (by intro d hd; cases hd)))
def cl_23307 : CNF.NClause := [(82,true),(6,false),(7,false),(8,false),(9,false)]
theorem der_23307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23307 :=
  CNF.rup_sound cl_23307 [cl_15239,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15239 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23308 : CNF.NClause := [(82,true),(9,false),(7,true),(6,false),(8,false)]
theorem der_23308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23308 :=
  CNF.rup_sound cl_23308 [cl_15242,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15242 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23309 : CNF.NClause := [(82,true),(8,true),(6,false),(7,false),(9,false)]
theorem der_23309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23309 :=
  CNF.rup_sound cl_23309 [cl_15246,cl_23275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15246 v h) (hints_cons _ _ _ (der_23275 v h) (by intro d hd; cases hd)))
def cl_23310 : CNF.NClause := [(82,true),(8,true),(6,false),(5,true),(9,false)]
theorem der_23310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23310 :=
  CNF.rup_sound cl_23310 [cl_15250,cl_23309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15250 v h) (hints_cons _ _ _ (der_23309 v h) (by intro d hd; cases hd)))
def cl_23311 : CNF.NClause := [(82,true),(6,false),(7,false),(8,false),(9,true)]
theorem der_23311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23311 :=
  CNF.rup_sound cl_23311 [cl_15253,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15253 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23312 : CNF.NClause := [(82,true),(8,false),(7,true),(6,false),(9,true)]
theorem der_23312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23312 :=
  CNF.rup_sound cl_23312 [cl_15256,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15256 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23313 : CNF.NClause := [(82,true),(6,false),(7,false),(8,true),(9,true)]
theorem der_23313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23313 :=
  CNF.rup_sound cl_23313 [cl_15260,cl_23276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15260 v h) (hints_cons _ _ _ (der_23276 v h) (by intro d hd; cases hd)))
def cl_23314 : CNF.NClause := [(82,true),(8,false),(6,true),(7,true),(9,false)]
theorem der_23314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23314 :=
  CNF.rup_sound cl_23314 [cl_15244,cl_23287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15244 v h) (hints_cons _ _ _ (der_23287 v h) (by intro d hd; cases hd)))
def cl_23315 : CNF.NClause := [(82,true),(9,false),(5,false),(7,true),(6,false)]
theorem der_23315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23315 :=
  CNF.rup_sound cl_23315 [cl_15249,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15249 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23316 : CNF.NClause := [(82,true),(9,true),(6,false),(7,true),(5,false)]
theorem der_23316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23316 :=
  CNF.rup_sound cl_23316 [cl_15263,cl_16262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15263 v h) (hints_cons _ _ _ (der_16262 v h) (by intro d hd; cases hd)))
def cl_23317 : CNF.NClause := [(64,true),(22,false),(2,false),(17,false),(7,true)]
theorem der_23317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23317 :=
  CNF.rup_sound cl_23317 [cl_15053,cl_14712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15053 v h) (hints_cons _ _ _ (der_14712 v h) (by intro d hd; cases hd)))
def cl_23318 : CNF.NClause := [(64,true),(22,false),(2,false),(7,true),(12,true)]
theorem der_23318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23318 :=
  CNF.rup_sound cl_23318 [cl_15061,cl_23317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15061 v h) (hints_cons _ _ _ (der_23317 v h) (by intro d hd; cases hd)))
def cl_23319 : CNF.NClause := [(64,true),(22,true),(2,false),(17,false),(7,true)]
theorem der_23319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23319 :=
  CNF.rup_sound cl_23319 [cl_15069,cl_23224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15069 v h) (hints_cons _ _ _ (der_23224 v h) (by intro d hd; cases hd)))
def cl_23320 : CNF.NClause := [(89,true),(27,false),(16,false),(14,true),(23,true)]
theorem der_23320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23320 :=
  CNF.rup_sound cl_23320 [cl_15324,cl_15323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15324 v h) (hints_cons _ _ _ (der_15323 v h) (by intro d hd; cases hd)))
def cl_23321 : CNF.NClause := [(89,true),(14,false),(27,true),(23,false),(7,true)]
theorem der_23321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23321 :=
  CNF.rup_sound cl_23321 [cl_15334,cl_23193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15334 v h) (hints_cons _ _ _ (der_23193 v h) (by intro d hd; cases hd)))
def cl_23322 : CNF.NClause := [(89,true),(16,true),(27,false),(7,true),(14,false)]
theorem der_23322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23322 :=
  CNF.rup_sound cl_23322 [cl_15326,cl_23189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15326 v h) (hints_cons _ _ _ (der_23189 v h) (by intro d hd; cases hd)))
def cl_23323 : CNF.NClause := [(67,true),(21,true),(23,false),(22,false),(24,false)]
theorem der_23323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23323 :=
  CNF.rup_sound cl_23323 [cl_15146,cl_15145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15146 v h) (hints_cons _ _ _ (der_15145 v h) (by intro d hd; cases hd)))
def cl_23324 : CNF.NClause := [(67,true),(20,true),(23,false),(21,false),(24,false)]
theorem der_23324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23324 :=
  CNF.rup_sound cl_23324 [cl_15148,cl_15144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15148 v h) (hints_cons _ _ _ (der_15144 v h) (by intro d hd; cases hd)))
def cl_23325 : CNF.NClause := [(67,true),(22,true),(24,false),(21,true),(23,false)]
theorem der_23325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23325 :=
  CNF.rup_sound cl_23325 [cl_15150,cl_23251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15150 v h) (hints_cons _ _ _ (der_23251 v h) (by intro d hd; cases hd)))
def cl_23326 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(24,false)]
theorem der_23326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23326 :=
  CNF.rup_sound cl_23326 [cl_15152,cl_15144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15152 v h) (hints_cons _ _ _ (der_15144 v h) (by intro d hd; cases hd)))
def cl_23327 : CNF.NClause := [(67,true),(22,false),(21,true),(23,true),(24,false)]
theorem der_23327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23327 :=
  CNF.rup_sound cl_23327 [cl_15154,cl_23252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15154 v h) (hints_cons _ _ _ (der_23252 v h) (by intro d hd; cases hd)))
def cl_23328 : CNF.NClause := [(67,true),(20,true),(22,true),(21,false),(24,false)]
theorem der_23328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23328 :=
  CNF.rup_sound cl_23328 [cl_15156,cl_23324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15156 v h) (hints_cons _ _ _ (der_23324 v h) (by intro d hd; cases hd)))
def cl_23329 : CNF.NClause := [(67,true),(20,true),(22,false),(23,false),(21,false)]
theorem der_23329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23329 :=
  CNF.rup_sound cl_23329 [cl_15160,cl_15144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15160 v h) (hints_cons _ _ _ (der_15144 v h) (by intro d hd; cases hd)))
def cl_23330 : CNF.NClause := [(67,true),(20,true),(23,false),(24,true),(22,false)]
theorem der_23330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23330 :=
  CNF.rup_sound cl_23330 [cl_15162,cl_23329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15162 v h) (hints_cons _ _ _ (der_23329 v h) (by intro d hd; cases hd)))
def cl_23331 : CNF.NClause := [(67,true),(20,true),(23,false),(22,true),(21,false)]
theorem der_23331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23331 :=
  CNF.rup_sound cl_23331 [cl_15164,cl_23328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15164 v h) (hints_cons _ _ _ (der_23328 v h) (by intro d hd; cases hd)))
def cl_23332 : CNF.NClause := [(67,true),(20,true),(21,false),(22,false),(24,true)]
theorem der_23332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23332 :=
  CNF.rup_sound cl_23332 [cl_15168,cl_23329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15168 v h) (hints_cons _ _ _ (der_23329 v h) (by intro d hd; cases hd)))
def cl_23333 : CNF.NClause := [(66,true),(21,false),(16,false),(11,false),(1,true)]
theorem der_23333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23333 :=
  CNF.rup_sound cl_23333 [cl_15112,cl_23299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15112 v h) (hints_cons _ _ _ (der_23299 v h) (by intro d hd; cases hd)))
def cl_23334 : CNF.NClause := [(66,true),(16,false),(6,false),(1,true),(21,false)]
theorem der_23334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23334 :=
  CNF.rup_sound cl_23334 [cl_15116,cl_23333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15116 v h) (hints_cons _ _ _ (der_23333 v h) (by intro d hd; cases hd)))
def cl_23335 : CNF.NClause := [(66,true),(16,true),(21,false),(11,false),(1,true)]
theorem der_23335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23335 :=
  CNF.rup_sound cl_23335 [cl_15120,cl_23300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15120 v h) (hints_cons _ _ _ (der_23300 v h) (by intro d hd; cases hd)))
def cl_23336 : CNF.NClause := [(66,true),(6,false),(1,true),(11,true),(21,false)]
theorem der_23336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23336 :=
  CNF.rup_sound cl_23336 [cl_15124,cl_23334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15124 v h) (hints_cons _ _ _ (der_23334 v h) (by intro d hd; cases hd)))
def cl_23337 : CNF.NClause := [(66,true),(21,true),(6,false),(11,false),(16,false)]
theorem der_23337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23337 :=
  CNF.rup_sound cl_23337 [cl_15128,cl_15127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15128 v h) (hints_cons _ _ _ (der_15127 v h) (by intro d hd; cases hd)))
def cl_23338 : CNF.NClause := [(66,true),(11,true),(6,false),(1,true),(16,false)]
theorem der_23338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23338 :=
  CNF.rup_sound cl_23338 [cl_15132,cl_23334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15132 v h) (hints_cons _ _ _ (der_23334 v h) (by intro d hd; cases hd)))
def cl_23339 : CNF.NClause := [(66,true),(16,true),(6,false),(11,false),(21,true)]
theorem der_23339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23339 :=
  CNF.rup_sound cl_23339 [cl_15136,cl_23263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15136 v h) (hints_cons _ _ _ (der_23263 v h) (by intro d hd; cases hd)))
def cl_23340 : CNF.NClause := [(11,true),(16,true),(66,false),(1,true),(21,true)]
theorem der_23340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23340 :=
  CNF.rup_sound cl_23340 [cl_15140,cl_23194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15140 v h) (hints_cons _ _ _ (der_23194 v h) (by intro d hd; cases hd)))
def cl_23341 : CNF.NClause := [(67,true),(20,false),(24,false),(22,false),(23,true)]
theorem der_23341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23341 :=
  CNF.rup_sound cl_23341 [cl_15151,cl_23252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15151 v h) (hints_cons _ _ _ (der_23252 v h) (by intro d hd; cases hd)))
def cl_23342 : CNF.NClause := [(67,true),(20,false),(21,false),(22,false),(23,true)]
theorem der_23342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23342 :=
  CNF.rup_sound cl_23342 [cl_15167,cl_23341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15167 v h) (hints_cons _ _ _ (der_23341 v h) (by intro d hd; cases hd)))
def cl_23343 : CNF.NClause := [(89,true),(7,true),(27,true),(16,false),(14,false)]
theorem der_23343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23343 :=
  CNF.rup_sound cl_23343 [cl_15338,cl_23193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15338 v h) (hints_cons _ _ _ (der_23193 v h) (by intro d hd; cases hd)))
def cl_23344 : CNF.NClause := [(89,true),(27,false),(7,false),(16,false),(23,true)]
theorem der_23344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23344 :=
  CNF.rup_sound cl_23344 [cl_15321,cl_23320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15321 v h) (hints_cons _ _ _ (der_23320 v h) (by intro d hd; cases hd)))
def cl_23345 : CNF.NClause := [(89,true),(7,false),(27,true),(16,false),(14,false)]
theorem der_23345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23345 :=
  CNF.rup_sound cl_23345 [cl_15337,cl_23193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15337 v h) (hints_cons _ _ _ (der_23193 v h) (by intro d hd; cases hd)))
def cl_23346 : CNF.NClause := [(66,false),(11,true),(1,true),(6,true),(21,true)]
theorem der_23346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23346 :=
  CNF.rup_sound cl_23346 [cl_15134,cl_23340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15134 v h) (hints_cons _ _ _ (der_23340 v h) (by intro d hd; cases hd)))
def cl_23347 : CNF.NClause := [(90,true),(28,true),(8,false),(11,false),(19,false)]
theorem der_23347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23347 :=
  CNF.rup_sound cl_23347 [cl_15361,cl_15369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15361 v h) (hints_cons _ _ _ (der_15369 v h) (by intro d hd; cases hd)))
def cl_23348 : CNF.NClause := [(64,true),(17,false),(2,false),(7,false),(22,false)]
theorem der_23348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23348 :=
  CNF.rup_sound cl_23348 [cl_15051,cl_14712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15051 v h) (hints_cons _ _ _ (der_14712 v h) (by intro d hd; cases hd)))
def cl_23349 : CNF.NClause := [(64,true),(17,true),(2,false),(12,true),(22,false)]
theorem der_23349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23349 :=
  CNF.rup_sound cl_23349 [cl_15059,cl_23318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15059 v h) (hints_cons _ _ _ (der_23318 v h) (by intro d hd; cases hd)))
def cl_23350 : CNF.NClause := [(64,true),(7,false),(2,false),(22,true),(17,false)]
theorem der_23350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23350 :=
  CNF.rup_sound cl_23350 [cl_15067,cl_23231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15067 v h) (hints_cons _ _ _ (der_23231 v h) (by intro d hd; cases hd)))
def cl_23351 : CNF.NClause := [(64,true),(7,false),(17,true),(2,false),(12,true)]
theorem der_23351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23351 :=
  CNF.rup_sound cl_23351 [cl_15075,cl_23349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15075 v h) (hints_cons _ _ _ (der_23349 v h) (by intro d hd; cases hd)))
def cl_23352 : CNF.NClause := [(64,false),(12,true),(2,true),(7,true),(22,true)]
theorem der_23352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23352 :=
  CNF.rup_sound cl_23352 [cl_15078,cl_15070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15078 v h) (hints_cons _ _ _ (der_15070 v h) (by intro d hd; cases hd)))
def cl_23353 : CNF.NClause := [(64,false),(12,true),(22,true),(17,true),(2,true)]
theorem der_23353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23353 :=
  CNF.rup_sound cl_23353 [cl_15076,cl_23352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15076 v h) (hints_cons _ _ _ (der_23352 v h) (by intro d hd; cases hd)))
def cl_23354 : CNF.NClause := [(91,true),(24,false),(6,false),(12,true),(26,false)]
theorem der_23354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23354 :=
  CNF.rup_sound cl_23354 [cl_15379,cl_23204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15379 v h) (hints_cons _ _ _ (der_23204 v h) (by intro d hd; cases hd)))
def cl_23355 : CNF.NClause := [(91,true),(24,false),(26,true),(12,true),(18,false)]
theorem der_23355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23355 :=
  CNF.rup_sound cl_23355 [cl_15395,cl_23306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15395 v h) (hints_cons _ _ _ (der_23306 v h) (by intro d hd; cases hd)))
def cl_23356 : CNF.NClause := [(91,true),(24,false),(6,false),(26,true),(18,true)]
theorem der_23356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23356 :=
  CNF.rup_sound cl_23356 [cl_15399,cl_23202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15399 v h) (hints_cons _ _ _ (der_23202 v h) (by intro d hd; cases hd)))
def cl_23357 : CNF.NClause := [(91,true),(26,true),(6,false),(12,true),(18,false)]
theorem der_23357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23357 :=
  CNF.rup_sound cl_23357 [cl_15403,cl_23355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15403 v h) (hints_cons _ _ _ (der_23355 v h) (by intro d hd; cases hd)))
def cl_23358 : CNF.NClause := [(72,false),(14,true),(13,true),(10,true),(12,true)]
theorem der_23358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23358 :=
  CNF.rup_sound cl_23358 [cl_15204,cl_23272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15204 v h) (hints_cons _ _ _ (der_23272 v h) (by intro d hd; cases hd)))
def cl_23359 : CNF.NClause := [(64,true),(22,false),(7,false),(17,false),(12,false)]
theorem der_23359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23359 :=
  CNF.rup_sound cl_23359 [cl_15049,cl_14712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15049 v h) (hints_cons _ _ _ (der_14712 v h) (by intro d hd; cases hd)))
def cl_23360 : CNF.NClause := [(64,true),(22,false),(7,false),(2,true),(17,false)]
theorem der_23360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23360 :=
  CNF.rup_sound cl_23360 [cl_15052,cl_23359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15052 v h) (hints_cons _ _ _ (der_23359 v h) (by intro d hd; cases hd)))
def cl_23361 : CNF.NClause := [(64,true),(22,false),(7,false),(2,true),(12,false)]
theorem der_23361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23361 :=
  CNF.rup_sound cl_23361 [cl_15056,cl_23360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15056 v h) (hints_cons _ _ _ (der_23360 v h) (by intro d hd; cases hd)))
def cl_23362 : CNF.NClause := [(64,true),(22,false),(7,false),(17,true),(2,true)]
theorem der_23362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23362 :=
  CNF.rup_sound cl_23362 [cl_15060,cl_23361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15060 v h) (hints_cons _ _ _ (der_23361 v h) (by intro d hd; cases hd)))
def cl_23363 : CNF.NClause := [(64,true),(17,false),(7,false),(22,true),(12,false)]
theorem der_23363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23363 :=
  CNF.rup_sound cl_23363 [cl_15064,cl_23231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15064 v h) (hints_cons _ _ _ (der_23231 v h) (by intro d hd; cases hd)))
def cl_23364 : CNF.NClause := [(64,true),(17,false),(7,false),(22,true),(2,true)]
theorem der_23364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23364 :=
  CNF.rup_sound cl_23364 [cl_15068,cl_23363] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15068 v h) (hints_cons _ _ _ (der_23363 v h) (by intro d hd; cases hd)))
def cl_23365 : CNF.NClause := [(64,true),(12,false),(7,false),(2,true),(17,true)]
theorem der_23365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23365 :=
  CNF.rup_sound cl_23365 [cl_15072,cl_23361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15072 v h) (hints_cons _ _ _ (der_23361 v h) (by intro d hd; cases hd)))
def cl_23366 : CNF.NClause := [(88,true),(29,true),(9,false),(13,false),(17,false)]
theorem der_23366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23366 :=
  CNF.rup_sound cl_23366 [cl_15299,cl_23246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15299 v h) (hints_cons _ _ _ (der_23246 v h) (by intro d hd; cases hd)))
def cl_23367 : CNF.NClause := [(91,true),(12,false),(26,false),(18,false),(24,true)]
theorem der_23367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23367 :=
  CNF.rup_sound cl_23367 [cl_15385,cl_23298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15385 v h) (hints_cons _ _ _ (der_23298 v h) (by intro d hd; cases hd)))
def cl_23368 : CNF.NClause := [(91,true),(12,false),(26,true),(18,false),(24,true)]
theorem der_23368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23368 :=
  CNF.rup_sound cl_23368 [cl_15401,cl_23298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15401 v h) (hints_cons _ _ _ (der_23298 v h) (by intro d hd; cases hd)))
def cl_23369 : CNF.NClause := [(63,true),(14,false),(4,false),(9,false),(19,false)]
theorem der_23369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23369 :=
  CNF.rup_sound cl_23369 [cl_15033,cl_23245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15033 v h) (hints_cons _ _ _ (der_23245 v h) (by intro d hd; cases hd)))
def cl_23370 : CNF.NClause := [(67,true),(21,false),(24,true),(23,false),(22,false)]
theorem der_23370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23370 :=
  CNF.rup_sound cl_23370 [cl_15159,cl_23329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15159 v h) (hints_cons _ _ _ (der_23329 v h) (by intro d hd; cases hd)))
def cl_23371 : CNF.NClause := [(91,true),(18,false),(6,false),(26,false),(24,true)]
theorem der_23371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23371 :=
  CNF.rup_sound cl_23371 [cl_15387,cl_23367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15387 v h) (hints_cons _ _ _ (der_23367 v h) (by intro d hd; cases hd)))
def cl_23372 : CNF.NClause := [(77,true),(16,true),(17,false),(15,true),(19,false)]
theorem der_23372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23372 :=
  CNF.rup_sound cl_23372 [cl_15210,cl_15218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15210 v h) (hints_cons _ _ _ (der_15218 v h) (by intro d hd; cases hd)))
def cl_23373 : CNF.NClause := [(77,true),(16,false),(17,false),(19,false),(18,false)]
theorem der_23373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23373 :=
  CNF.rup_sound cl_23373 [cl_15208,cl_23230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15208 v h) (hints_cons _ _ _ (der_23230 v h) (by intro d hd; cases hd)))
def cl_23374 : CNF.NClause := [(77,true),(18,false),(15,true),(19,false),(16,false)]
theorem der_23374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23374 :=
  CNF.rup_sound cl_23374 [cl_15212,cl_23373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15212 v h) (hints_cons _ _ _ (der_23373 v h) (by intro d hd; cases hd)))
def cl_23375 : CNF.NClause := [(77,true),(15,true),(17,false),(19,false),(18,true)]
theorem der_23375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23375 :=
  CNF.rup_sound cl_23375 [cl_15216,cl_15218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15216 v h) (hints_cons _ _ _ (der_15218 v h) (by intro d hd; cases hd)))
def cl_23376 : CNF.NClause := [(77,true),(15,true),(16,false),(19,false),(17,true)]
theorem der_23376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23376 :=
  CNF.rup_sound cl_23376 [cl_15220,cl_23374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15220 v h) (hints_cons _ _ _ (der_23374 v h) (by intro d hd; cases hd)))
def cl_23377 : CNF.NClause := [(77,true),(15,true),(17,false),(16,false),(18,false)]
theorem der_23377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23377 :=
  CNF.rup_sound cl_23377 [cl_15224,cl_23374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15224 v h) (hints_cons _ _ _ (der_23374 v h) (by intro d hd; cases hd)))
def cl_23378 : CNF.NClause := [(77,true),(15,true),(16,false),(17,true),(18,false)]
theorem der_23378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23378 :=
  CNF.rup_sound cl_23378 [cl_15228,cl_23374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15228 v h) (hints_cons _ _ _ (der_23374 v h) (by intro d hd; cases hd)))
def cl_23379 : CNF.NClause := [(77,true),(15,true),(19,true),(17,false),(16,false)]
theorem der_23379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23379 :=
  CNF.rup_sound cl_23379 [cl_15232,cl_23377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15232 v h) (hints_cons _ _ _ (der_23377 v h) (by intro d hd; cases hd)))
def cl_23380 : CNF.NClause := [(77,true),(15,true),(19,true),(17,false),(18,false)]
theorem der_23380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23380 :=
  CNF.rup_sound cl_23380 [cl_15226,cl_23377] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15226 v h) (hints_cons _ _ _ (der_23377 v h) (by intro d hd; cases hd)))
def cl_23381 : CNF.NClause := [(66,true),(11,true),(1,false),(16,false),(21,false)]
theorem der_23381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23381 :=
  CNF.rup_sound cl_23381 [cl_15115,cl_23280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15115 v h) (hints_cons _ _ _ (der_23280 v h) (by intro d hd; cases hd)))
def cl_23382 : CNF.NClause := [(66,true),(11,true),(6,false),(16,true),(21,false)]
theorem der_23382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23382 :=
  CNF.rup_sound cl_23382 [cl_15123,cl_23336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15123 v h) (hints_cons _ _ _ (der_23336 v h) (by intro d hd; cases hd)))
def cl_23383 : CNF.NClause := [(66,true),(1,false),(6,false),(16,false),(21,true)]
theorem der_23383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23383 :=
  CNF.rup_sound cl_23383 [cl_15131,cl_15127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15131 v h) (hints_cons _ _ _ (der_15127 v h) (by intro d hd; cases hd)))
def cl_23384 : CNF.NClause := [(66,true),(1,false),(6,false),(16,true),(21,true)]
theorem der_23384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23384 :=
  CNF.rup_sound cl_23384 [cl_15139,cl_23263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15139 v h) (hints_cons _ _ _ (der_23263 v h) (by intro d hd; cases hd)))
def cl_23385 : CNF.NClause := [(90,true),(19,false),(8,false),(22,false),(28,false)]
theorem der_23385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23385 :=
  CNF.rup_sound cl_23385 [cl_15347,cl_15345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15347 v h) (hints_cons _ _ _ (der_15345 v h) (by intro d hd; cases hd)))
def cl_23386 : CNF.NClause := [(90,true),(11,true),(8,false),(28,false),(22,false)]
theorem der_23386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23386 :=
  CNF.rup_sound cl_23386 [cl_15351,cl_23385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15351 v h) (hints_cons _ _ _ (der_23385 v h) (by intro d hd; cases hd)))
def cl_23387 : CNF.NClause := [(90,true),(11,true),(8,false),(28,false),(19,false)]
theorem der_23387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23387 :=
  CNF.rup_sound cl_23387 [cl_15355,cl_23385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15355 v h) (hints_cons _ _ _ (der_23385 v h) (by intro d hd; cases hd)))
def cl_23388 : CNF.NClause := [(90,true),(11,true),(8,false),(28,false),(22,true)]
theorem der_23388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23388 :=
  CNF.rup_sound cl_23388 [cl_15359,cl_23387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15359 v h) (hints_cons _ _ _ (der_23387 v h) (by intro d hd; cases hd)))
def cl_23389 : CNF.NClause := [(90,true),(11,true),(8,false),(22,false),(19,false)]
theorem der_23389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23389 :=
  CNF.rup_sound cl_23389 [cl_15363,cl_23385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15363 v h) (hints_cons _ _ _ (der_23385 v h) (by intro d hd; cases hd)))
def cl_23390 : CNF.NClause := [(90,true),(11,true),(8,false),(19,true),(22,false)]
theorem der_23390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23390 :=
  CNF.rup_sound cl_23390 [cl_15367,cl_23386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15367 v h) (hints_cons _ _ _ (der_23386 v h) (by intro d hd; cases hd)))
def cl_23391 : CNF.NClause := [(90,true),(8,false),(28,true),(19,false),(22,true)]
theorem der_23391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23391 :=
  CNF.rup_sound cl_23391 [cl_15371,cl_15369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15371 v h) (hints_cons _ _ _ (der_15369 v h) (by intro d hd; cases hd)))
def cl_23392 : CNF.NClause := [(72,true),(10,false),(12,false),(13,false),(14,false)]
theorem der_23392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23392 :=
  CNF.rup_sound cl_23392 [cl_15177,cl_23242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15177 v h) (hints_cons _ _ _ (der_23242 v h) (by intro d hd; cases hd)))
def cl_23393 : CNF.NClause := [(72,true),(10,false),(12,true),(13,false),(14,false)]
theorem der_23393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23393 :=
  CNF.rup_sound cl_23393 [cl_15181,cl_23237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15181 v h) (hints_cons _ _ _ (der_23237 v h) (by intro d hd; cases hd)))
def cl_23394 : CNF.NClause := [(72,true),(11,true),(10,false),(12,false),(14,false)]
theorem der_23394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23394 :=
  CNF.rup_sound cl_23394 [cl_15185,cl_23392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15185 v h) (hints_cons _ _ _ (der_23392 v h) (by intro d hd; cases hd)))
def cl_23395 : CNF.NClause := [(72,true),(11,true),(10,false),(13,true),(14,false)]
theorem der_23395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23395 :=
  CNF.rup_sound cl_23395 [cl_15189,cl_23394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15189 v h) (hints_cons _ _ _ (der_23394 v h) (by intro d hd; cases hd)))
def cl_23396 : CNF.NClause := [(72,true),(11,true),(10,false),(12,false),(13,false)]
theorem der_23396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23396 :=
  CNF.rup_sound cl_23396 [cl_15193,cl_23392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15193 v h) (hints_cons _ _ _ (der_23392 v h) (by intro d hd; cases hd)))
def cl_23397 : CNF.NClause := [(72,true),(10,false),(12,true),(13,false),(14,true)]
theorem der_23397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23397 :=
  CNF.rup_sound cl_23397 [cl_15197,cl_15195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15197 v h) (hints_cons _ _ _ (der_15195 v h) (by intro d hd; cases hd)))
def cl_23398 : CNF.NClause := [(72,true),(11,true),(10,false),(12,false),(13,true)]
theorem der_23398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23398 :=
  CNF.rup_sound cl_23398 [cl_15201,cl_23394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15201 v h) (hints_cons _ _ _ (der_23394 v h) (by intro d hd; cases hd)))
def cl_23399 : CNF.NClause := [(90,true),(8,true),(22,false),(28,false),(19,false)]
theorem der_23399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23399 :=
  CNF.rup_sound cl_23399 [cl_15348,cl_23210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15348 v h) (hints_cons _ _ _ (der_23210 v h) (by intro d hd; cases hd)))
def cl_23400 : CNF.NClause := [(90,true),(28,false),(22,true),(11,true),(19,false)]
theorem der_23400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23400 :=
  CNF.rup_sound cl_23400 [cl_15356,cl_23387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15356 v h) (hints_cons _ _ _ (der_23387 v h) (by intro d hd; cases hd)))
def cl_23401 : CNF.NClause := [(90,true),(8,true),(22,false),(28,true),(19,false)]
theorem der_23401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23401 :=
  CNF.rup_sound cl_23401 [cl_15364,cl_23210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15364 v h) (hints_cons _ _ _ (der_23210 v h) (by intro d hd; cases hd)))
def cl_23402 : CNF.NClause := [(66,true),(16,false),(21,false),(6,true),(11,true)]
theorem der_23402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23402 :=
  CNF.rup_sound cl_23402 [cl_15118,cl_23280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15118 v h) (hints_cons _ _ _ (der_23280 v h) (by intro d hd; cases hd)))
def cl_23403 : CNF.NClause := [(72,true),(13,false),(14,false),(12,false),(11,true)]
theorem der_23403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23403 :=
  CNF.rup_sound cl_23403 [cl_15178,cl_23392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15178 v h) (hints_cons _ _ _ (der_23392 v h) (by intro d hd; cases hd)))
def cl_23404 : CNF.NClause := [(72,true),(13,true),(14,false),(12,false),(11,true)]
theorem der_23404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23404 :=
  CNF.rup_sound cl_23404 [cl_15186,cl_23394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15186 v h) (hints_cons _ _ _ (der_23394 v h) (by intro d hd; cases hd)))
def cl_23405 : CNF.NClause := [(72,true),(12,false),(10,true),(11,true),(13,false)]
theorem der_23405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23405 :=
  CNF.rup_sound cl_23405 [cl_15194,cl_23403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15194 v h) (hints_cons _ _ _ (der_23403 v h) (by intro d hd; cases hd)))
def cl_23406 : CNF.NClause := [(90,true),(8,true),(22,false),(28,false),(19,true)]
theorem der_23406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23406 :=
  CNF.rup_sound cl_23406 [cl_15352,cl_23278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15352 v h) (hints_cons _ _ _ (der_23278 v h) (by intro d hd; cases hd)))
def cl_23407 : CNF.NClause := [(65,true),(23,false),(13,false),(18,false),(3,true)]
theorem der_23407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23407 :=
  CNF.rup_sound cl_23407 [cl_15080,cl_23234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15080 v h) (hints_cons _ _ _ (der_23234 v h) (by intro d hd; cases hd)))
def cl_23408 : CNF.NClause := [(65,true),(23,false),(8,false),(18,false),(3,true)]
theorem der_23408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23408 :=
  CNF.rup_sound cl_23408 [cl_15084,cl_23407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15084 v h) (hints_cons _ _ _ (der_23407 v h) (by intro d hd; cases hd)))
def cl_23409 : CNF.NClause := [(65,true),(23,false),(3,true),(8,false),(13,false)]
theorem der_23409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23409 :=
  CNF.rup_sound cl_23409 [cl_15088,cl_23407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15088 v h) (hints_cons _ _ _ (der_23407 v h) (by intro d hd; cases hd)))
def cl_23410 : CNF.NClause := [(65,true),(8,false),(3,true),(18,true),(23,false)]
theorem der_23410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23410 :=
  CNF.rup_sound cl_23410 [cl_15092,cl_23409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15092 v h) (hints_cons _ _ _ (der_23409 v h) (by intro d hd; cases hd)))
def cl_23411 : CNF.NClause := [(65,true),(18,false),(3,true),(8,false),(13,false)]
theorem der_23411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23411 :=
  CNF.rup_sound cl_23411 [cl_15096,cl_23407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15096 v h) (hints_cons _ _ _ (der_23407 v h) (by intro d hd; cases hd)))
def cl_23412 : CNF.NClause := [(65,true),(13,true),(8,false),(18,false),(3,true)]
theorem der_23412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23412 :=
  CNF.rup_sound cl_23412 [cl_15100,cl_23408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15100 v h) (hints_cons _ _ _ (der_23408 v h) (by intro d hd; cases hd)))
def cl_23413 : CNF.NClause := [(65,true),(8,false),(3,true),(13,false),(18,true)]
theorem der_23413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23413 :=
  CNF.rup_sound cl_23413 [cl_15104,cl_23409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15104 v h) (hints_cons _ _ _ (der_23409 v h) (by intro d hd; cases hd)))
def cl_23414 : CNF.NClause := [(90,true),(28,true),(22,false),(8,false),(11,false)]
theorem der_23414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23414 :=
  CNF.rup_sound cl_23414 [cl_15365,cl_23347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15365 v h) (hints_cons _ _ _ (der_23347 v h) (by intro d hd; cases hd)))
def cl_23415 : CNF.NClause := [(90,true),(8,true),(28,true),(11,false),(22,false)]
theorem der_23415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23415 :=
  CNF.rup_sound cl_23415 [cl_15366,cl_23210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15366 v h) (hints_cons _ _ _ (der_23210 v h) (by intro d hd; cases hd)))
def cl_23416 : CNF.NClause := [(91,true),(18,false),(6,true),(26,false),(24,true)]
theorem der_23416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23416 :=
  CNF.rup_sound cl_23416 [cl_15388,cl_23298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15388 v h) (hints_cons _ _ _ (der_23298 v h) (by intro d hd; cases hd)))
def cl_23417 : CNF.NClause := [(91,true),(26,true),(24,false),(6,false),(12,false)]
theorem der_23417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23417 :=
  CNF.rup_sound cl_23417 [cl_15393,cl_23202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15393 v h) (hints_cons _ _ _ (der_23202 v h) (by intro d hd; cases hd)))
def cl_23418 : CNF.NClause := [(91,true),(26,false),(24,false),(6,false),(12,false)]
theorem der_23418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23418 :=
  CNF.rup_sound cl_23418 [cl_15377,cl_23202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15377 v h) (hints_cons _ _ _ (der_23202 v h) (by intro d hd; cases hd)))
def cl_23419 : CNF.NClause := [(72,true),(14,false),(13,false),(11,false),(12,false)]
theorem der_23419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23419 :=
  CNF.rup_sound cl_23419 [cl_15176,cl_23392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15176 v h) (hints_cons _ _ _ (der_23392 v h) (by intro d hd; cases hd)))
def cl_23420 : CNF.NClause := [(72,true),(14,false),(13,false),(11,false),(12,true)]
theorem der_23420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23420 :=
  CNF.rup_sound cl_23420 [cl_15180,cl_23237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15180 v h) (hints_cons _ _ _ (der_23237 v h) (by intro d hd; cases hd)))
def cl_23421 : CNF.NClause := [(72,true),(14,false),(12,false),(10,true),(13,true)]
theorem der_23421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23421 :=
  CNF.rup_sound cl_23421 [cl_15184,cl_23404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15184 v h) (hints_cons _ _ _ (der_23404 v h) (by intro d hd; cases hd)))
def cl_23422 : CNF.NClause := [(72,true),(14,false),(11,false),(12,true),(10,true)]
theorem der_23422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23422 :=
  CNF.rup_sound cl_23422 [cl_15188,cl_23420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15188 v h) (hints_cons _ _ _ (der_23420 v h) (by intro d hd; cases hd)))
def cl_23423 : CNF.NClause := [(72,true),(11,false),(13,false),(10,true),(12,false)]
theorem der_23423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23423 :=
  CNF.rup_sound cl_23423 [cl_15192,cl_23419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15192 v h) (hints_cons _ _ _ (der_23419 v h) (by intro d hd; cases hd)))
def cl_23424 : CNF.NClause := [(72,true),(14,true),(12,true),(13,false),(11,false)]
theorem der_23424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23424 :=
  CNF.rup_sound cl_23424 [cl_15196,cl_15195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15196 v h) (hints_cons _ _ _ (der_15195 v h) (by intro d hd; cases hd)))
def cl_23425 : CNF.NClause := [(72,true),(14,true),(11,false),(12,false),(10,true)]
theorem der_23425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23425 :=
  CNF.rup_sound cl_23425 [cl_15200,cl_23423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15200 v h) (hints_cons _ _ _ (der_23423 v h) (by intro d hd; cases hd)))
def cl_23426 : CNF.NClause := [(72,true),(13,false),(12,true),(11,true),(14,false)]
theorem der_23426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23426 :=
  CNF.rup_sound cl_23426 [cl_15182,cl_23393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15182 v h) (hints_cons _ _ _ (der_23393 v h) (by intro d hd; cases hd)))
def cl_23427 : CNF.NClause := [(63,true),(24,false),(14,false),(19,false),(9,false)]
theorem der_23427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23427 :=
  CNF.rup_sound cl_23427 [cl_15018,cl_23245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15018 v h) (hints_cons _ _ _ (der_23245 v h) (by intro d hd; cases hd)))
def cl_23428 : CNF.NClause := [(63,true),(24,false),(14,true),(19,false),(9,false)]
theorem der_23428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23428 :=
  CNF.rup_sound cl_23428 [cl_15022,cl_23249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15022 v h) (hints_cons _ _ _ (der_23249 v h) (by intro d hd; cases hd)))
def cl_23429 : CNF.NClause := [(63,true),(24,false),(14,false),(19,true),(9,false)]
theorem der_23429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23429 :=
  CNF.rup_sound cl_23429 [cl_15026,cl_15025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15026 v h) (hints_cons _ _ _ (der_15025 v h) (by intro d hd; cases hd)))
def cl_23430 : CNF.NClause := [(63,true),(24,false),(4,true),(14,true),(9,false)]
theorem der_23430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23430 :=
  CNF.rup_sound cl_23430 [cl_15030,cl_23428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15030 v h) (hints_cons _ _ _ (der_23428 v h) (by intro d hd; cases hd)))
def cl_23431 : CNF.NClause := [(63,true),(14,false),(4,true),(19,false),(9,false)]
theorem der_23431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23431 :=
  CNF.rup_sound cl_23431 [cl_15034,cl_23427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15034 v h) (hints_cons _ _ _ (der_23427 v h) (by intro d hd; cases hd)))
def cl_23432 : CNF.NClause := [(63,true),(24,true),(14,true),(9,false),(19,false)]
theorem der_23432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23432 :=
  CNF.rup_sound cl_23432 [cl_15038,cl_23249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15038 v h) (hints_cons _ _ _ (der_23249 v h) (by intro d hd; cases hd)))
def cl_23433 : CNF.NClause := [(63,true),(14,false),(19,true),(9,false),(4,true)]
theorem der_23433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23433 :=
  CNF.rup_sound cl_23433 [cl_15042,cl_23429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15042 v h) (hints_cons _ _ _ (der_23429 v h) (by intro d hd; cases hd)))
def cl_23434 : CNF.NClause := [(63,false),(4,true),(19,true),(9,true),(24,true)]
theorem der_23434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23434 :=
  CNF.rup_sound cl_23434 [cl_15044,cl_23244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15044 v h) (hints_cons _ _ _ (der_23244 v h) (by intro d hd; cases hd)))
def cl_23435 : CNF.NClause := [(90,true),(28,false),(22,false),(19,true),(11,false)]
theorem der_23435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23435 :=
  CNF.rup_sound cl_23435 [cl_15349,cl_23278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15349 v h) (hints_cons _ _ _ (der_23278 v h) (by intro d hd; cases hd)))
def cl_23436 : CNF.NClause := [(90,true),(28,false),(22,true),(11,false),(19,true)]
theorem der_23436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23436 :=
  CNF.rup_sound cl_23436 [cl_15357,cl_23279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15357 v h) (hints_cons _ _ _ (der_23279 v h) (by intro d hd; cases hd)))
def cl_23437 : CNF.NClause := [(90,true),(28,true),(22,true),(8,false),(11,false)]
theorem der_23437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23437 :=
  CNF.rup_sound cl_23437 [cl_15373,cl_15369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15373 v h) (hints_cons _ _ _ (der_15369 v h) (by intro d hd; cases hd)))
def cl_23438 : CNF.NClause := [(63,true),(14,false),(4,false),(9,false),(19,true)]
theorem der_23438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23438 :=
  CNF.rup_sound cl_23438 [cl_15041,cl_15025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15041 v h) (hints_cons _ _ _ (der_15025 v h) (by intro d hd; cases hd)))
def cl_23439 : CNF.NClause := [(63,true),(24,false),(4,true),(19,false),(14,false)]
theorem der_23439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23439 :=
  CNF.rup_sound cl_23439 [cl_15020,cl_23427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15020 v h) (hints_cons _ _ _ (der_23427 v h) (by intro d hd; cases hd)))
def cl_23440 : CNF.NClause := [(63,true),(24,false),(4,true),(19,true),(14,false)]
theorem der_23440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23440 :=
  CNF.rup_sound cl_23440 [cl_15028,cl_23429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15028 v h) (hints_cons _ _ _ (der_23429 v h) (by intro d hd; cases hd)))
def cl_23441 : CNF.NClause := [(63,true),(14,false),(4,true),(19,false),(24,true)]
theorem der_23441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23441 :=
  CNF.rup_sound cl_23441 [cl_15036,cl_23431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15036 v h) (hints_cons _ _ _ (der_23431 v h) (by intro d hd; cases hd)))
def cl_23442 : CNF.NClause := [(89,true),(7,false),(14,false),(23,true),(27,true)]
theorem der_23442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23442 :=
  CNF.rup_sound cl_23442 [cl_15341,cl_23345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15341 v h) (hints_cons _ _ _ (der_23345 v h) (by intro d hd; cases hd)))
def cl_23443 : CNF.NClause := [(89,true),(27,false),(7,true),(16,false),(23,true)]
theorem der_23443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23443 :=
  CNF.rup_sound cl_23443 [cl_15322,cl_23320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15322 v h) (hints_cons _ _ _ (der_23320 v h) (by intro d hd; cases hd)))
def cl_23444 : CNF.NClause := [(89,true),(7,false),(16,true),(14,false),(23,true)]
theorem der_23444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23444 :=
  CNF.rup_sound cl_23444 [cl_15325,cl_23442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15325 v h) (hints_cons _ _ _ (der_23442 v h) (by intro d hd; cases hd)))
def cl_23445 : CNF.NClause := [(89,true),(14,false),(7,false),(27,true),(23,false)]
theorem der_23445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23445 :=
  CNF.rup_sound cl_23445 [cl_15333,cl_23193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15333 v h) (hints_cons _ _ _ (der_23193 v h) (by intro d hd; cases hd)))
def cl_23446 : CNF.NClause := [(64,true),(7,false),(2,false),(12,false),(22,true)]
theorem der_23446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23446 :=
  CNF.rup_sound cl_23446 [cl_15071,cl_23231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15071 v h) (hints_cons _ _ _ (der_23231 v h) (by intro d hd; cases hd)))
def cl_23447 : CNF.NClause := [(77,true),(16,true),(15,false),(18,false),(19,false)]
theorem der_23447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23447 :=
  CNF.rup_sound cl_23447 [cl_15213,cl_15209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15213 v h) (hints_cons _ _ _ (der_15209 v h) (by intro d hd; cases hd)))
def cl_23448 : CNF.NClause := [(77,true),(19,false),(16,true),(15,false),(18,true)]
theorem der_23448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23448 :=
  CNF.rup_sound cl_23448 [cl_15221,cl_23227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15221 v h) (hints_cons _ _ _ (der_23227 v h) (by intro d hd; cases hd)))
def cl_23449 : CNF.NClause := [(77,true),(19,true),(18,false),(16,true),(15,false)]
theorem der_23449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23449 :=
  CNF.rup_sound cl_23449 [cl_15229,cl_23228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15229 v h) (hints_cons _ _ _ (der_23228 v h) (by intro d hd; cases hd)))
def cl_23450 : CNF.NClause := [(77,true),(19,false),(15,true),(17,true),(18,false)]
theorem der_23450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23450 :=
  CNF.rup_sound cl_23450 [cl_15214,cl_23374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15214 v h) (hints_cons _ _ _ (der_23374 v h) (by intro d hd; cases hd)))
def cl_23451 : CNF.NClause := [(77,true),(19,false),(15,false),(16,false),(18,false)]
theorem der_23451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23451 :=
  CNF.rup_sound cl_23451 [cl_15211,cl_23230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15211 v h) (hints_cons _ _ _ (der_23230 v h) (by intro d hd; cases hd)))
def cl_23452 : CNF.NClause := [(77,true),(19,false),(18,true),(15,false),(16,false)]
theorem der_23452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23452 :=
  CNF.rup_sound cl_23452 [cl_15219,cl_15215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15219 v h) (hints_cons _ _ _ (der_15215 v h) (by intro d hd; cases hd)))
def cl_23453 : CNF.NClause := [(77,true),(16,false),(15,false),(17,true),(18,false)]
theorem der_23453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23453 :=
  CNF.rup_sound cl_23453 [cl_15227,cl_23451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15227 v h) (hints_cons _ _ _ (der_23451 v h) (by intro d hd; cases hd)))
def cl_23454 : CNF.NClause := [(77,true),(19,true),(16,false),(15,false),(18,true)]
theorem der_23454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23454 :=
  CNF.rup_sound cl_23454 [cl_15235,cl_23229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15235 v h) (hints_cons _ _ _ (der_23229 v h) (by intro d hd; cases hd)))
def cl_23455 : CNF.NClause := [(64,true),(12,false),(2,false),(22,true),(7,true)]
theorem der_23455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23455 :=
  CNF.rup_sound cl_23455 [cl_15073,cl_23224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15073 v h) (hints_cons _ _ _ (der_23224 v h) (by intro d hd; cases hd)))
def cl_23456 : CNF.NClause := [(64,true),(22,false),(2,true),(17,true),(12,false)]
theorem der_23456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23456 :=
  CNF.rup_sound cl_23456 [cl_15058,cl_23361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15058 v h) (hints_cons _ _ _ (der_23361 v h) (by intro d hd; cases hd)))
def cl_23457 : CNF.NClause := [(65,true),(18,false),(8,false),(3,false),(23,false)]
theorem der_23457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23457 :=
  CNF.rup_sound cl_23457 [cl_15083,cl_23233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15083 v h) (hints_cons _ _ _ (der_23233 v h) (by intro d hd; cases hd)))
def cl_23458 : CNF.NClause := [(65,true),(13,true),(3,false),(8,false),(23,false)]
theorem der_23458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23458 :=
  CNF.rup_sound cl_23458 [cl_15091,cl_23457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15091 v h) (hints_cons _ _ _ (der_23457 v h) (by intro d hd; cases hd)))
def cl_23459 : CNF.NClause := [(65,true),(23,true),(3,false),(8,false),(18,false)]
theorem der_23459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23459 :=
  CNF.rup_sound cl_23459 [cl_15099,cl_23238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15099 v h) (hints_cons _ _ _ (der_23238 v h) (by intro d hd; cases hd)))
def cl_23460 : CNF.NClause := [(65,true),(23,true),(3,false),(8,false),(13,true)]
theorem der_23460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23460 :=
  CNF.rup_sound cl_23460 [cl_15107,cl_23459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15107 v h) (hints_cons _ _ _ (der_23459 v h) (by intro d hd; cases hd)))
def cl_23461 : CNF.NClause := [(65,true),(3,true),(18,false),(8,true),(23,false)]
theorem der_23461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23461 :=
  CNF.rup_sound cl_23461 [cl_15086,cl_23234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15086 v h) (hints_cons _ _ _ (der_23234 v h) (by intro d hd; cases hd)))
def cl_23462 : CNF.NClause := [(88,true),(9,false),(17,false),(21,true),(29,true)]
theorem der_23462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23462 :=
  CNF.rup_sound cl_23462 [cl_15309,cl_23246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15309 v h) (hints_cons _ _ _ (der_23246 v h) (by intro d hd; cases hd)))
def cl_23463 : CNF.NClause := [(65,true),(8,true),(3,false),(18,false),(23,false)]
theorem der_23463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23463 :=
  CNF.rup_sound cl_23463 [cl_15085,cl_15081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15085 v h) (hints_cons _ _ _ (der_15081 v h) (by intro d hd; cases hd)))
def cl_23464 : CNF.NClause := [(65,true),(8,true),(3,false),(18,true),(23,false)]
theorem der_23464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23464 :=
  CNF.rup_sound cl_23464 [cl_15093,cl_23207] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15093 v h) (hints_cons _ _ _ (der_23207 v h) (by intro d hd; cases hd)))
def cl_23465 : CNF.NClause := [(71,true),(20,false),(1,false),(19,true),(26,false)]
theorem der_23465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23465 :=
  CNF.rup_sound cl_23465 [cl_16144,cl_23241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_16144 v h) (hints_cons _ _ _ (der_23241 v h) (by intro d hd; cases hd)))
def cl_23466 : CNF.NClause := [(71,true),(1,false),(26,false),(19,false),(20,false)]
theorem der_23466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23466 :=
  CNF.rup_sound cl_23466 [cl_16191,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_16191 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_23467 : CNF.NClause := [(72,true),(14,false),(10,false),(11,false),(12,false)]
theorem der_23467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23467 :=
  CNF.rup_sound cl_23467 [cl_15183,cl_23392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15183 v h) (hints_cons _ _ _ (der_23392 v h) (by intro d hd; cases hd)))
def cl_23468 : CNF.NClause := [(72,true),(14,false),(10,false),(12,true),(11,false)]
theorem der_23468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23468 :=
  CNF.rup_sound cl_23468 [cl_15187,cl_23237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15187 v h) (hints_cons _ _ _ (der_23237 v h) (by intro d hd; cases hd)))
def cl_23469 : CNF.NClause := [(72,true),(13,true),(10,false),(12,false),(14,true)]
theorem der_23469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23469 :=
  CNF.rup_sound cl_23469 [cl_15199,cl_23398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15199 v h) (hints_cons _ _ _ (der_23398 v h) (by intro d hd; cases hd)))
def cl_23470 : CNF.NClause := [(72,true),(10,false),(12,true),(11,false),(14,true)]
theorem der_23470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23470 :=
  CNF.rup_sound cl_23470 [cl_15203,cl_15195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15203 v h) (hints_cons _ _ _ (der_15195 v h) (by intro d hd; cases hd)))
def cl_23471 : CNF.NClause := [(63,true),(4,false),(14,false),(19,false),(24,false)]
theorem der_23471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23471 :=
  CNF.rup_sound cl_23471 [cl_15019,cl_23245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15019 v h) (hints_cons _ _ _ (der_23245 v h) (by intro d hd; cases hd)))
def cl_23472 : CNF.NClause := [(63,true),(4,false),(14,false),(19,true),(24,false)]
theorem der_23472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23472 :=
  CNF.rup_sound cl_23472 [cl_15027,cl_15025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15027 v h) (hints_cons _ _ _ (der_15025 v h) (by intro d hd; cases hd)))
def cl_23473 : CNF.NClause := [(63,true),(4,false),(14,false),(19,false),(24,true)]
theorem der_23473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23473 :=
  CNF.rup_sound cl_23473 [cl_15035,cl_23369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15035 v h) (hints_cons _ _ _ (der_23369 v h) (by intro d hd; cases hd)))
def cl_23474 : CNF.NClause := [(63,true),(4,false),(14,false),(19,true),(24,true)]
theorem der_23474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23474 :=
  CNF.rup_sound cl_23474 [cl_15043,cl_23438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15043 v h) (hints_cons _ _ _ (der_23438 v h) (by intro d hd; cases hd)))
def cl_23475 : CNF.NClause := [(63,true),(4,false),(14,true),(19,false),(24,false)]
theorem der_23475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23475 :=
  CNF.rup_sound cl_23475 [cl_15023,cl_23249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15023 v h) (hints_cons _ _ _ (der_23249 v h) (by intro d hd; cases hd)))
def cl_23476 : CNF.NClause := [(63,true),(4,false),(14,true),(19,true),(24,false)]
theorem der_23476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23476 :=
  CNF.rup_sound cl_23476 [cl_15031,cl_23248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15031 v h) (hints_cons _ _ _ (der_23248 v h) (by intro d hd; cases hd)))
def cl_23477 : CNF.NClause := [(63,true),(4,false),(14,true),(19,false),(24,true)]
theorem der_23477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23477 :=
  CNF.rup_sound cl_23477 [cl_15039,cl_23249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15039 v h) (hints_cons _ _ _ (der_23249 v h) (by intro d hd; cases hd)))
def cl_23478 : CNF.NClause := [(63,true),(14,true),(4,true),(19,false),(24,false)]
theorem der_23478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23478 :=
  CNF.rup_sound cl_23478 [cl_15024,cl_23428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15024 v h) (hints_cons _ _ _ (der_23428 v h) (by intro d hd; cases hd)))
def cl_23479 : CNF.NClause := [(67,true),(24,false),(23,true),(22,true),(21,false)]
theorem der_23479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23479 :=
  CNF.rup_sound cl_23479 [cl_15155,cl_23328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15155 v h) (hints_cons _ _ _ (der_23328 v h) (by intro d hd; cases hd)))
def cl_23480 : CNF.NClause := [(67,true),(20,false),(22,true),(24,true),(23,false)]
theorem der_23480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23480 :=
  CNF.rup_sound cl_23480 [cl_15163,cl_23255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15163 v h) (hints_cons _ _ _ (der_23255 v h) (by intro d hd; cases hd)))
def cl_23481 : CNF.NClause := [(67,true),(20,false),(23,true),(22,true),(21,false)]
theorem der_23481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23481 :=
  CNF.rup_sound cl_23481 [cl_15171,cl_23479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15171 v h) (hints_cons _ _ _ (der_23479 v h) (by intro d hd; cases hd)))
def cl_23482 : CNF.NClause := [(67,true),(20,false),(24,false),(23,false),(22,false)]
theorem der_23482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23482 :=
  CNF.rup_sound cl_23482 [cl_15143,cl_15145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15143 v h) (hints_cons _ _ _ (der_15145 v h) (by intro d hd; cases hd)))
def cl_23483 : CNF.NClause := [(67,true),(20,false),(22,true),(24,false),(23,false)]
theorem der_23483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23483 :=
  CNF.rup_sound cl_23483 [cl_15147,cl_23251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15147 v h) (hints_cons _ _ _ (der_23251 v h) (by intro d hd; cases hd)))
def cl_23484 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,false)]
theorem der_23484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23484 :=
  CNF.rup_sound cl_23484 [cl_15111,cl_15127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15111 v h) (hints_cons _ _ _ (der_15127 v h) (by intro d hd; cases hd)))
def cl_23485 : CNF.NClause := [(88,true),(17,false),(9,false),(13,false),(21,false)]
theorem der_23485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23485 :=
  CNF.rup_sound cl_23485 [cl_15283,cl_23366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15283 v h) (hints_cons _ _ _ (der_23366 v h) (by intro d hd; cases hd)))
def cl_23486 : CNF.NClause := [(88,true),(29,false),(17,false),(13,false),(21,false)]
theorem der_23486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23486 :=
  CNF.rup_sound cl_23486 [cl_15284,cl_23485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15284 v h) (hints_cons _ _ _ (der_23485 v h) (by intro d hd; cases hd)))
def cl_23487 : CNF.NClause := [(88,true),(29,false),(17,true),(13,false),(9,true)]
theorem der_23487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23487 :=
  CNF.rup_sound cl_23487 [cl_15288,cl_23257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15288 v h) (hints_cons _ _ _ (der_23257 v h) (by intro d hd; cases hd)))
def cl_23488 : CNF.NClause := [(88,true),(17,false),(29,true),(13,false),(9,true)]
theorem der_23488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23488 :=
  CNF.rup_sound cl_23488 [cl_15300,cl_15308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15300 v h) (hints_cons _ _ _ (der_15308 v h) (by intro d hd; cases hd)))
def cl_23489 : CNF.NClause := [(88,true),(21,false),(13,false),(17,true),(9,true)]
theorem der_23489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23489 :=
  CNF.rup_sound cl_23489 [cl_15304,cl_23487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15304 v h) (hints_cons _ _ _ (der_23487 v h) (by intro d hd; cases hd)))
def cl_23490 : CNF.NClause := [(88,true),(29,false),(9,false),(17,true),(13,false)]
theorem der_23490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23490 :=
  CNF.rup_sound cl_23490 [cl_15287,cl_23257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15287 v h) (hints_cons _ _ _ (der_23257 v h) (by intro d hd; cases hd)))
def cl_23491 : CNF.NClause := [(88,true),(29,true),(21,false),(9,false),(13,false)]
theorem der_23491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23491 :=
  CNF.rup_sound cl_23491 [cl_15303,cl_23485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15303 v h) (hints_cons _ _ _ (der_23485 v h) (by intro d hd; cases hd)))
def cl_23492 : CNF.NClause := [(88,true),(29,true),(13,true),(9,false),(17,false)]
theorem der_23492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23492 :=
  CNF.rup_sound cl_23492 [cl_15301,cl_23462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15301 v h) (hints_cons _ _ _ (der_23462 v h) (by intro d hd; cases hd)))
def cl_23493 : CNF.NClause := [(88,true),(29,false),(9,false),(17,false),(21,false)]
theorem der_23493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23493 :=
  CNF.rup_sound cl_23493 [cl_15285,cl_23485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15285 v h) (hints_cons _ _ _ (der_23485 v h) (by intro d hd; cases hd)))
def cl_23494 : CNF.NClause := [(88,true),(29,false),(17,false),(13,true),(21,false)]
theorem der_23494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23494 :=
  CNF.rup_sound cl_23494 [cl_15286,cl_23493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15286 v h) (hints_cons _ _ _ (der_23493 v h) (by intro d hd; cases hd)))
def cl_23495 : CNF.NClause := [(88,true),(9,true),(17,true),(21,false),(29,false)]
theorem der_23495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23495 :=
  CNF.rup_sound cl_23495 [cl_15290,cl_23489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15290 v h) (hints_cons _ _ _ (der_23489 v h) (by intro d hd; cases hd)))
def cl_23496 : CNF.NClause := [(88,true),(29,false),(9,false),(13,true),(17,true)]
theorem der_23496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23496 :=
  CNF.rup_sound cl_23496 [cl_15289,cl_23258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15289 v h) (hints_cons _ _ _ (der_23258 v h) (by intro d hd; cases hd)))
def cl_23497 : CNF.NClause := [(88,true),(29,true),(21,false),(9,false),(17,true)]
theorem der_23497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23497 :=
  CNF.rup_sound cl_23497 [cl_15305,cl_23491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15305 v h) (hints_cons _ _ _ (der_23491 v h) (by intro d hd; cases hd)))
def cl_23498 : CNF.NClause := [(88,true),(29,true),(17,false),(21,false),(9,true)]
theorem der_23498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23498 :=
  CNF.rup_sound cl_23498 [cl_15302,cl_23488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15302 v h) (hints_cons _ _ _ (der_23488 v h) (by intro d hd; cases hd)))
def cl_23499 : CNF.NClause := [(73,true),(10,false),(18,false),(4,false),(28,false)]
theorem der_23499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23499 :=
  CNF.rup_sound cl_23499 [cl_14716,cl_23262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14716 v h) (hints_cons _ _ _ (der_23262 v h) (by intro d hd; cases hd)))
def cl_23500 : CNF.NClause := [(66,true),(1,false),(6,false),(11,false),(16,true)]
theorem der_23500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23500 :=
  CNF.rup_sound cl_23500 [cl_15119,cl_23263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15119 v h) (hints_cons _ _ _ (der_23263 v h) (by intro d hd; cases hd)))
def cl_23501 : CNF.NClause := [(79,true),(8,false),(2,true),(21,false),(26,false),(15,false)]
theorem der_23501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23501 :=
  CNF.rup_sound cl_23501 [cl_1094,cl_1090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1094 v h) (hints_cons _ _ _ (inp_1090 v h) (by intro d hd; cases hd)))
def cl_23502 : CNF.NClause := [(79,true),(8,false),(2,true),(14,false),(21,false),(26,false)]
theorem der_23502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23502 :=
  CNF.rup_sound cl_23502 [cl_1098,cl_1090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1098 v h) (hints_cons _ _ _ (inp_1090 v h) (by intro d hd; cases hd)))
def cl_23503 : CNF.NClause := [(79,true),(8,false),(2,true),(26,false),(21,false),(14,true)]
theorem der_23503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23503 :=
  CNF.rup_sound cl_23503 [cl_1102,cl_23501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1102 v h) (hints_cons _ _ _ (der_23501 v h) (by intro d hd; cases hd)))
def cl_23504 : CNF.NClause := [(79,true),(15,false),(8,false),(2,true),(26,false),(14,false)]
theorem der_23504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23504 :=
  CNF.rup_sound cl_23504 [cl_1106,cl_1090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1106 v h) (hints_cons _ _ _ (inp_1090 v h) (by intro d hd; cases hd)))
def cl_23505 : CNF.NClause := [(79,true),(8,false),(2,true),(15,false),(26,false),(14,true)]
theorem der_23505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23505 :=
  CNF.rup_sound cl_23505 [cl_1110,cl_23501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1110 v h) (hints_cons _ _ _ (der_23501 v h) (by intro d hd; cases hd)))
def cl_23506 : CNF.NClause := [(79,true),(15,true),(8,false),(2,true),(14,false),(26,false)]
theorem der_23506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23506 :=
  CNF.rup_sound cl_23506 [cl_1114,cl_23502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1114 v h) (hints_cons _ _ _ (der_23502 v h) (by intro d hd; cases hd)))
def cl_23507 : CNF.NClause := [(79,true),(15,true),(8,false),(2,true),(26,false),(14,true)]
theorem der_23507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23507 :=
  CNF.rup_sound cl_23507 [cl_1118,cl_23503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1118 v h) (hints_cons _ _ _ (der_23503 v h) (by intro d hd; cases hd)))
def cl_23508 : CNF.NClause := [(79,true),(15,false),(8,false),(2,true),(21,false),(14,false)]
theorem der_23508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23508 :=
  CNF.rup_sound cl_23508 [cl_1122,cl_1090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1122 v h) (hints_cons _ _ _ (inp_1090 v h) (by intro d hd; cases hd)))
def cl_23509 : CNF.NClause := [(79,true),(8,false),(2,true),(14,true),(15,false),(21,false)]
theorem der_23509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23509 :=
  CNF.rup_sound cl_23509 [cl_1126,cl_23501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1126 v h) (hints_cons _ _ _ (der_23501 v h) (by intro d hd; cases hd)))
def cl_23510 : CNF.NClause := [(79,true),(15,true),(8,false),(2,true),(14,false),(21,false)]
theorem der_23510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23510 :=
  CNF.rup_sound cl_23510 [cl_1130,cl_23502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1130 v h) (hints_cons _ _ _ (der_23502 v h) (by intro d hd; cases hd)))
def cl_23511 : CNF.NClause := [(79,true),(15,true),(8,false),(2,true),(14,true),(21,false)]
theorem der_23511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23511 :=
  CNF.rup_sound cl_23511 [cl_1134,cl_23503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1134 v h) (hints_cons _ _ _ (der_23503 v h) (by intro d hd; cases hd)))
def cl_23512 : CNF.NClause := [(79,true),(15,false),(8,false),(2,true),(14,false),(21,true)]
theorem der_23512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23512 :=
  CNF.rup_sound cl_23512 [cl_1138,cl_23504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1138 v h) (hints_cons _ _ _ (der_23504 v h) (by intro d hd; cases hd)))
def cl_23513 : CNF.NClause := [(79,true),(21,true),(8,false),(2,true),(15,false),(14,true)]
theorem der_23513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23513 :=
  CNF.rup_sound cl_23513 [cl_1142,cl_23505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1142 v h) (hints_cons _ _ _ (der_23505 v h) (by intro d hd; cases hd)))
def cl_23514 : CNF.NClause := [(79,true),(15,true),(8,false),(2,true),(14,false),(26,true)]
theorem der_23514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23514 :=
  CNF.rup_sound cl_23514 [cl_1146,cl_23510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1146 v h) (hints_cons _ _ _ (der_23510 v h) (by intro d hd; cases hd)))
def cl_23515 : CNF.NClause := [(68,true),(29,false),(4,false),(8,false),(12,true),(20,false)]
theorem der_23515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23515 :=
  CNF.rup_sound cl_23515 [cl_397,cl_389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_397 v h) (hints_cons _ _ _ (inp_389 v h) (by intro d hd; cases hd)))
def cl_23516 : CNF.NClause := [(68,true),(4,false),(12,true),(8,false),(16,false),(29,false)]
theorem der_23516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23516 :=
  CNF.rup_sound cl_23516 [cl_405,cl_389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_405 v h) (hints_cons _ _ _ (inp_389 v h) (by intro d hd; cases hd)))
def cl_23517 : CNF.NClause := [(68,true),(16,true),(4,false),(8,false),(12,true),(29,false)]
theorem der_23517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23517 :=
  CNF.rup_sound cl_23517 [cl_413,cl_23515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_413 v h) (hints_cons _ _ _ (der_23515 v h) (by intro d hd; cases hd)))
def cl_23518 : CNF.NClause := [(68,true),(20,false),(4,false),(8,false),(16,false),(12,true)]
theorem der_23518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23518 :=
  CNF.rup_sound cl_23518 [cl_421,cl_389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_421 v h) (hints_cons _ _ _ (inp_389 v h) (by intro d hd; cases hd)))
def cl_23519 : CNF.NClause := [(68,true),(4,false),(8,false),(16,true),(12,true),(20,false)]
theorem der_23519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23519 :=
  CNF.rup_sound cl_23519 [cl_429,cl_23515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_429 v h) (hints_cons _ _ _ (der_23515 v h) (by intro d hd; cases hd)))
def cl_23520 : CNF.NClause := [(68,true),(20,true),(4,false),(8,false),(16,false),(12,true)]
theorem der_23520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23520 :=
  CNF.rup_sound cl_23520 [cl_437,cl_23516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_437 v h) (hints_cons _ _ _ (der_23516 v h) (by intro d hd; cases hd)))
def cl_23521 : CNF.NClause := [(68,true),(16,true),(12,true),(8,false),(20,true),(4,false)]
theorem der_23521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23521 :=
  CNF.rup_sound cl_23521 [cl_445,cl_23517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_445 v h) (hints_cons _ _ _ (der_23517 v h) (by intro d hd; cases hd)))
def cl_23522 : CNF.NClause := [(79,true),(14,false),(8,false),(21,false),(15,false),(26,true)]
theorem der_23522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23522 :=
  CNF.rup_sound cl_23522 [cl_1121,cl_23508] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1121 v h) (hints_cons _ _ _ (der_23508 v h) (by intro d hd; cases hd)))
def cl_23523 : CNF.NClause := [(74,true),(6,false),(23,true),(19,true),(2,true),(29,false)]
theorem der_23523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23523 :=
  CNF.rup_sound cl_23523 [cl_798,cl_794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_798 v h) (hints_cons _ _ _ (inp_794 v h) (by intro d hd; cases hd)))
def cl_23524 : CNF.NClause := [(74,true),(2,true),(6,false),(19,false),(23,false),(29,true)]
theorem der_23524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23524 :=
  CNF.rup_sound cl_23524 [cl_806,cl_802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_806 v h) (hints_cons _ _ _ (inp_802 v h) (by intro d hd; cases hd)))
def cl_23525 : CNF.NClause := [(74,true),(23,false),(6,false),(2,true),(10,false),(29,true)]
theorem der_23525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23525 :=
  CNF.rup_sound cl_23525 [cl_810,cl_802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_810 v h) (hints_cons _ _ _ (inp_802 v h) (by intro d hd; cases hd)))
def cl_23526 : CNF.NClause := [(74,true),(6,false),(2,true),(10,true),(23,false),(29,true)]
theorem der_23526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23526 :=
  CNF.rup_sound cl_23526 [cl_814,cl_23524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_814 v h) (hints_cons _ _ _ (der_23524 v h) (by intro d hd; cases hd)))
def cl_23527 : CNF.NClause := [(74,true),(29,true),(2,true),(10,false),(19,false),(6,false)]
theorem der_23527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23527 :=
  CNF.rup_sound cl_23527 [cl_818,cl_802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_818 v h) (hints_cons _ _ _ (inp_802 v h) (by intro d hd; cases hd)))
def cl_23528 : CNF.NClause := [(74,true),(29,true),(2,true),(10,true),(19,false),(6,false)]
theorem der_23528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23528 :=
  CNF.rup_sound cl_23528 [cl_822,cl_23524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_822 v h) (hints_cons _ _ _ (der_23524 v h) (by intro d hd; cases hd)))
def cl_23529 : CNF.NClause := [(74,true),(23,true),(2,true),(10,false),(19,true),(6,false)]
theorem der_23529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23529 :=
  CNF.rup_sound cl_23529 [cl_826,cl_794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_826 v h) (hints_cons _ _ _ (inp_794 v h) (by intro d hd; cases hd)))
def cl_23530 : CNF.NClause := [(83,true),(23,false),(5,false),(4,true),(11,true),(26,false)]
theorem der_23530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23530 :=
  CNF.rup_sound cl_23530 [cl_1358,cl_1350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1358 v h) (hints_cons _ _ _ (inp_1350 v h) (by intro d hd; cases hd)))
def cl_23531 : CNF.NClause := [(83,true),(11,true),(26,false),(4,true),(17,false),(5,false)]
theorem der_23531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23531 :=
  CNF.rup_sound cl_23531 [cl_1366,cl_1350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1366 v h) (hints_cons _ _ _ (inp_1350 v h) (by intro d hd; cases hd)))
def cl_23532 : CNF.NClause := [(83,true),(17,true),(11,true),(4,true),(5,false),(26,false)]
theorem der_23532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23532 :=
  CNF.rup_sound cl_23532 [cl_1374,cl_23530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1374 v h) (hints_cons _ _ _ (der_23530 v h) (by intro d hd; cases hd)))
def cl_23533 : CNF.NClause := [(83,true),(23,false),(5,false),(17,false),(4,true),(11,true)]
theorem der_23533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23533 :=
  CNF.rup_sound cl_23533 [cl_1382,cl_1350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1382 v h) (hints_cons _ _ _ (inp_1350 v h) (by intro d hd; cases hd)))
def cl_23534 : CNF.NClause := [(83,true),(17,true),(4,true),(5,false),(11,true),(23,false)]
theorem der_23534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23534 :=
  CNF.rup_sound cl_23534 [cl_1390,cl_23530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1390 v h) (hints_cons _ _ _ (der_23530 v h) (by intro d hd; cases hd)))
def cl_23535 : CNF.NClause := [(73,true),(7,false),(10,false),(21,false),(18,false),(28,false)]
theorem der_23535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23535 :=
  CNF.rup_sound cl_23535 [cl_706,cl_23499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_706 v h) (hints_cons _ _ _ (der_23499 v h) (by intro d hd; cases hd)))
def cl_23536 : CNF.NClause := [(73,true),(4,true),(7,false),(21,false),(18,false),(28,false)]
theorem der_23536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23536 :=
  CNF.rup_sound cl_23536 [cl_710,cl_23535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_710 v h) (hints_cons _ _ _ (der_23535 v h) (by intro d hd; cases hd)))
def cl_23537 : CNF.NClause := [(73,true),(7,false),(21,false),(10,false),(4,true),(28,false)]
theorem der_23537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23537 :=
  CNF.rup_sound cl_23537 [cl_714,cl_23535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_714 v h) (hints_cons _ _ _ (der_23535 v h) (by intro d hd; cases hd)))
def cl_23538 : CNF.NClause := [(73,true),(28,false),(7,false),(10,true),(4,true),(21,false)]
theorem der_23538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23538 :=
  CNF.rup_sound cl_23538 [cl_718,cl_23536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_718 v h) (hints_cons _ _ _ (der_23536 v h) (by intro d hd; cases hd)))
def cl_23539 : CNF.NClause := [(73,true),(7,false),(10,false),(18,false),(21,true),(28,false)]
theorem der_23539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23539 :=
  CNF.rup_sound cl_23539 [cl_722,cl_23262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_722 v h) (hints_cons _ _ _ (der_23262 v h) (by intro d hd; cases hd)))
def cl_23540 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(28,false)]
theorem der_23540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23540 :=
  CNF.rup_sound cl_23540 [cl_726,cl_23536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_726 v h) (hints_cons _ _ _ (der_23536 v h) (by intro d hd; cases hd)))
def cl_23541 : CNF.NClause := [(73,true),(21,true),(7,false),(10,false),(18,true),(28,false)]
theorem der_23541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23541 :=
  CNF.rup_sound cl_23541 [cl_730,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_730 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_23542 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(21,true),(28,false)]
theorem der_23542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23542 :=
  CNF.rup_sound cl_23542 [cl_734,cl_23540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_734 v h) (hints_cons _ _ _ (der_23540 v h) (by intro d hd; cases hd)))
def cl_23543 : CNF.NClause := [(73,true),(10,false),(7,false),(18,false),(4,true),(21,false)]
theorem der_23543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23543 :=
  CNF.rup_sound cl_23543 [cl_738,cl_23535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_738 v h) (hints_cons _ _ _ (der_23535 v h) (by intro d hd; cases hd)))
def cl_23544 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,false)]
theorem der_23544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23544 :=
  CNF.rup_sound cl_23544 [cl_742,cl_23536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_742 v h) (hints_cons _ _ _ (der_23536 v h) (by intro d hd; cases hd)))
def cl_23545 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(18,true),(21,false)]
theorem der_23545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23545 :=
  CNF.rup_sound cl_23545 [cl_746,cl_23537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_746 v h) (hints_cons _ _ _ (der_23537 v h) (by intro d hd; cases hd)))
def cl_23546 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,true),(21,false)]
theorem der_23546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23546 :=
  CNF.rup_sound cl_23546 [cl_750,cl_23538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_750 v h) (hints_cons _ _ _ (der_23538 v h) (by intro d hd; cases hd)))
def cl_23547 : CNF.NClause := [(73,true),(7,false),(10,false),(18,false),(4,true),(28,true)]
theorem der_23547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23547 :=
  CNF.rup_sound cl_23547 [cl_754,cl_23543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_754 v h) (hints_cons _ _ _ (der_23543 v h) (by intro d hd; cases hd)))
def cl_23548 : CNF.NClause := [(73,true),(4,true),(7,false),(10,true),(18,false),(21,true)]
theorem der_23548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23548 :=
  CNF.rup_sound cl_23548 [cl_758,cl_23540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_758 v h) (hints_cons _ _ _ (der_23540 v h) (by intro d hd; cases hd)))
def cl_23549 : CNF.NClause := [(73,true),(4,true),(7,false),(10,false),(21,true),(28,true)]
theorem der_23549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23549 :=
  CNF.rup_sound cl_23549 [cl_762,cl_23547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_762 v h) (hints_cons _ _ _ (der_23547 v h) (by intro d hd; cases hd)))
def cl_23550 : CNF.NClause := [(83,true),(17,false),(26,true),(5,false),(11,false),(23,false)]
theorem der_23550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23550 :=
  CNF.rup_sound cl_23550 [cl_1377,cl_1378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1377 v h) (hints_cons _ _ _ (inp_1378 v h) (by intro d hd; cases hd)))
def cl_23551 : CNF.NClause := [(81,true),(12,false),(9,false),(28,true),(15,false),(23,false)]
theorem der_23551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23551 :=
  CNF.rup_sound cl_23551 [cl_1249,cl_1250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1249 v h) (hints_cons _ _ _ (inp_1250 v h) (by intro d hd; cases hd)))
def cl_23552 : CNF.NClause := [(74,true),(6,false),(2,true),(19,true),(10,false),(29,false)]
theorem der_23552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23552 :=
  CNF.rup_sound cl_23552 [cl_778,cl_794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_778 v h) (hints_cons _ _ _ (inp_794 v h) (by intro d hd; cases hd)))
def cl_23553 : CNF.NClause := [(81,true),(12,false),(1,false),(15,false),(23,false),(28,true)]
theorem der_23553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23553 :=
  CNF.rup_sound cl_23553 [cl_1251,cl_23551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1251 v h) (hints_cons _ _ _ (der_23551 v h) (by intro d hd; cases hd)))
def cl_23554 : CNF.NClause := [(68,true),(16,true),(4,false),(12,true),(20,true),(29,false)]
theorem der_23554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23554 :=
  CNF.rup_sound cl_23554 [cl_415,cl_23517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_415 v h) (hints_cons _ _ _ (der_23517 v h) (by intro d hd; cases hd)))
def cl_23555 : CNF.NClause := [(75,true),(10,false),(3,true),(9,false),(16,true),(26,false)]
theorem der_23555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23555 :=
  CNF.rup_sound cl_23555 [cl_858,cl_842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_858 v h) (hints_cons _ _ _ (inp_842 v h) (by intro d hd; cases hd)))
def cl_23556 : CNF.NClause := [(75,true),(22,false),(3,true),(9,false),(10,false),(16,true)]
theorem der_23556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23556 :=
  CNF.rup_sound cl_23556 [cl_874,cl_842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_874 v h) (hints_cons _ _ _ (inp_842 v h) (by intro d hd; cases hd)))
def cl_23557 : CNF.NClause := [(75,true),(10,false),(3,true),(9,false),(22,true),(16,true)]
theorem der_23557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23557 :=
  CNF.rup_sound cl_23557 [cl_890,cl_23555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_890 v h) (hints_cons _ _ _ (der_23555 v h) (by intro d hd; cases hd)))
def cl_23558 : CNF.NClause := [(75,true),(10,false),(26,true),(9,false),(22,false),(16,true)]
theorem der_23558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23558 :=
  CNF.rup_sound cl_23558 [cl_873,cl_23556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_873 v h) (hints_cons _ _ _ (der_23556 v h) (by intro d hd; cases hd)))
def cl_23559 : CNF.NClause := [(75,true),(26,true),(22,true),(10,false),(9,false),(16,true)]
theorem der_23559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23559 :=
  CNF.rup_sound cl_23559 [cl_889,cl_23557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_889 v h) (hints_cons _ _ _ (der_23557 v h) (by intro d hd; cases hd)))
def cl_23560 : CNF.NClause := [(68,true),(16,true),(4,false),(29,false),(8,false),(20,false)]
theorem der_23560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23560 :=
  CNF.rup_sound cl_23560 [cl_393,cl_23515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_393 v h) (hints_cons _ _ _ (der_23515 v h) (by intro d hd; cases hd)))
def cl_23561 : CNF.NClause := [(68,true),(16,true),(4,false),(29,false),(8,false),(20,true)]
theorem der_23561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23561 :=
  CNF.rup_sound cl_23561 [cl_409,cl_23517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_409 v h) (hints_cons _ _ _ (der_23517 v h) (by intro d hd; cases hd)))
def cl_23562 : CNF.NClause := [(68,true),(20,false),(4,false),(8,false),(29,true),(16,true)]
theorem der_23562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23562 :=
  CNF.rup_sound cl_23562 [cl_425,cl_23519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_425 v h) (hints_cons _ _ _ (der_23519 v h) (by intro d hd; cases hd)))
def cl_23563 : CNF.NClause := [(68,true),(16,true),(4,false),(8,false),(29,true),(20,true)]
theorem der_23563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23563 :=
  CNF.rup_sound cl_23563 [cl_441,cl_23521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_441 v h) (hints_cons _ _ _ (der_23521 v h) (by intro d hd; cases hd)))
def cl_23564 : CNF.NClause := [(68,true),(20,false),(4,false),(29,false),(12,true),(16,true)]
theorem der_23564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23564 :=
  CNF.rup_sound cl_23564 [cl_399,cl_23515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_399 v h) (hints_cons _ _ _ (der_23515 v h) (by intro d hd; cases hd)))
def cl_23565 : CNF.NClause := [(75,true),(16,true),(3,true),(9,false),(22,false),(26,false)]
theorem der_23565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23565 :=
  CNF.rup_sound cl_23565 [cl_846,cl_842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_846 v h) (hints_cons _ _ _ (inp_842 v h) (by intro d hd; cases hd)))
def cl_23566 : CNF.NClause := [(75,true),(16,true),(26,true),(3,true),(9,false),(22,false)]
theorem der_23566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23566 :=
  CNF.rup_sound cl_23566 [cl_878,cl_23556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_878 v h) (hints_cons _ _ _ (der_23556 v h) (by intro d hd; cases hd)))
def cl_23567 : CNF.NClause := [(75,true),(16,true),(3,true),(22,true),(26,false),(9,false)]
theorem der_23567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23567 :=
  CNF.rup_sound cl_23567 [cl_862,cl_23555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_862 v h) (hints_cons _ _ _ (der_23555 v h) (by intro d hd; cases hd)))
def cl_23568 : CNF.NClause := [(75,true),(26,true),(10,false),(3,false),(22,false),(16,true)]
theorem der_23568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23568 :=
  CNF.rup_sound cl_23568 [cl_875,cl_23558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_875 v h) (hints_cons _ _ _ (der_23558 v h) (by intro d hd; cases hd)))
def cl_23569 : CNF.NClause := [(81,true),(12,false),(1,false),(15,true),(9,true),(28,false)]
theorem der_23569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23569 :=
  CNF.rup_sound cl_23569 [cl_1243,cl_1227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1243 v h) (hints_cons _ _ _ (inp_1227 v h) (by intro d hd; cases hd)))
def cl_23570 : CNF.NClause := [(81,true),(12,false),(23,false),(28,true),(9,true),(1,false)]
theorem der_23570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23570 :=
  CNF.rup_sound cl_23570 [cl_1259,cl_23553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1259 v h) (hints_cons _ _ _ (der_23553 v h) (by intro d hd; cases hd)))
def cl_23571 : CNF.NClause := [(79,true),(15,false),(21,false),(2,true),(14,false),(26,true)]
theorem der_23571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23571 :=
  CNF.rup_sound cl_23571 [cl_1124,cl_23508] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1124 v h) (hints_cons _ _ _ (der_23508 v h) (by intro d hd; cases hd)))
def cl_23572 : CNF.NClause := [(75,true),(9,true),(3,false),(10,false),(22,false),(26,true)]
theorem der_23572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23572 :=
  CNF.rup_sound cl_23572 [cl_867,cl_23568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_867 v h) (hints_cons _ _ _ (der_23568 v h) (by intro d hd; cases hd)))
def cl_23573 : CNF.NClause := [(73,true),(28,false),(4,false),(7,true),(18,true),(21,true)]
theorem der_23573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23573 :=
  CNF.rup_sound cl_23573 [cl_735,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_735 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_23574 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(18,true),(21,false)]
theorem der_23574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23574 :=
  CNF.rup_sound cl_23574 [cl_751,cl_719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_751 v h) (hints_cons _ _ _ (inp_719 v h) (by intro d hd; cases hd)))
def cl_23575 : CNF.NClause := [(69,true),(11,true),(2,true),(27,false),(9,false),(18,true)]
theorem der_23575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23575 :=
  CNF.rup_sound cl_23575 [cl_478,cl_462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_478 v h) (hints_cons _ _ _ (inp_462 v h) (by intro d hd; cases hd)))
def cl_23576 : CNF.NClause := [(69,true),(2,true),(9,false),(11,true),(20,false),(18,true)]
theorem der_23576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23576 :=
  CNF.rup_sound cl_23576 [cl_494,cl_462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_494 v h) (hints_cons _ _ _ (inp_462 v h) (by intro d hd; cases hd)))
def cl_23577 : CNF.NClause := [(73,true),(10,false),(7,false),(28,true),(21,false),(18,true)]
theorem der_23577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23577 :=
  CNF.rup_sound cl_23577 [cl_745,cl_23545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_745 v h) (hints_cons _ _ _ (der_23545 v h) (by intro d hd; cases hd)))
def cl_23578 : CNF.NClause := [(73,true),(10,false),(4,false),(7,false),(21,true),(18,true)]
theorem der_23578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23578 :=
  CNF.rup_sound cl_23578 [cl_761,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_761 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_23579 : CNF.NClause := [(69,true),(27,false),(2,true),(9,false),(18,true),(20,false)]
theorem der_23579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23579 :=
  CNF.rup_sound cl_23579 [cl_458,cl_462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_458 v h) (hints_cons _ _ _ (inp_462 v h) (by intro d hd; cases hd)))
def cl_23580 : CNF.NClause := [(69,true),(2,true),(18,true),(27,false),(9,false),(20,true)]
theorem der_23580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23580 :=
  CNF.rup_sound cl_23580 [cl_474,cl_23575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_474 v h) (hints_cons _ _ _ (der_23575 v h) (by intro d hd; cases hd)))
def cl_23581 : CNF.NClause := [(69,true),(20,false),(2,true),(9,false),(27,true),(18,true)]
theorem der_23581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23581 :=
  CNF.rup_sound cl_23581 [cl_490,cl_23576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_490 v h) (hints_cons _ _ _ (der_23576 v h) (by intro d hd; cases hd)))
def cl_23582 : CNF.NClause := [(69,true),(18,true),(2,true),(9,false),(11,false),(20,true)]
theorem der_23582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23582 :=
  CNF.rup_sound cl_23582 [cl_506,cl_23580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_506 v h) (hints_cons _ _ _ (der_23580 v h) (by intro d hd; cases hd)))
def cl_23583 : CNF.NClause := [(69,true),(20,true),(11,false),(9,false),(18,true),(27,false)]
theorem der_23583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23583 :=
  CNF.rup_sound cl_23583 [cl_473,cl_23580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_473 v h) (hints_cons _ _ _ (der_23580 v h) (by intro d hd; cases hd)))
def cl_23584 : CNF.NClause := [(69,true),(20,false),(27,true),(11,false),(9,false),(18,true)]
theorem der_23584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23584 :=
  CNF.rup_sound cl_23584 [cl_489,cl_23581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_489 v h) (hints_cons _ _ _ (der_23581 v h) (by intro d hd; cases hd)))
def cl_23585 : CNF.NClause := [(69,true),(20,true),(2,false),(11,false),(9,false),(18,true)]
theorem der_23585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23585 :=
  CNF.rup_sound cl_23585 [cl_505,cl_23583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_505 v h) (hints_cons _ _ _ (der_23583 v h) (by intro d hd; cases hd)))
def cl_23586 : CNF.NClause := [(69,true),(18,true),(2,true),(11,false),(27,false),(20,true)]
theorem der_23586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23586 :=
  CNF.rup_sound cl_23586 [cl_476,cl_23580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_476 v h) (hints_cons _ _ _ (der_23580 v h) (by intro d hd; cases hd)))
def cl_23587 : CNF.NClause := [(69,true),(27,true),(2,true),(11,false),(20,false),(18,true)]
theorem der_23587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23587 :=
  CNF.rup_sound cl_23587 [cl_492,cl_23581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_492 v h) (hints_cons _ _ _ (der_23581 v h) (by intro d hd; cases hd)))
def cl_23588 : CNF.NClause := [(86,true),(5,false),(18,true),(29,true),(1,false),(14,true)]
theorem der_23588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23588 :=
  CNF.rup_sound cl_23588 [cl_1597,cl_1581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1597 v h) (hints_cons _ _ _ (inp_1581 v h) (by intro d hd; cases hd)))
def cl_23589 : CNF.NClause := [(73,true),(4,false),(7,true),(28,true),(21,false),(18,true)]
theorem der_23589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23589 :=
  CNF.rup_sound cl_23589 [cl_747,cl_23574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_747 v h) (hints_cons _ _ _ (der_23574 v h) (by intro d hd; cases hd)))
def cl_23590 : CNF.NClause := [(73,true),(10,false),(4,false),(7,true),(21,true),(18,true)]
theorem der_23590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23590 :=
  CNF.rup_sound cl_23590 [cl_763,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_763 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_23591 : CNF.NClause := [(73,true),(4,true),(18,true),(10,false),(21,false),(28,false)]
theorem der_23591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23591 :=
  CNF.rup_sound cl_23591 [cl_716,cl_23537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_716 v h) (hints_cons _ _ _ (der_23537 v h) (by intro d hd; cases hd)))
def cl_23592 : CNF.NClause := [(73,true),(18,true),(7,true),(10,false),(21,true),(28,false)]
theorem der_23592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23592 :=
  CNF.rup_sound cl_23592 [cl_732,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_732 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_23593 : CNF.NClause := [(73,true),(10,false),(7,true),(18,false),(21,false),(28,false)]
theorem der_23593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23593 :=
  CNF.rup_sound cl_23593 [cl_708,cl_23499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_708 v h) (hints_cons _ _ _ (der_23499 v h) (by intro d hd; cases hd)))
def cl_23594 : CNF.NClause := [(76,true),(10,false),(1,true),(8,true),(17,false),(24,false)]
theorem der_23594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23594 :=
  CNF.rup_sound cl_23594 [cl_932,cl_900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_932 v h) (hints_cons _ _ _ (inp_900 v h) (by intro d hd; cases hd)))
def cl_23595 : CNF.NClause := [(73,true),(10,false),(4,false),(7,false),(21,false),(18,false)]
theorem der_23595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23595 :=
  CNF.rup_sound cl_23595 [cl_737,cl_23499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_737 v h) (hints_cons _ _ _ (der_23499 v h) (by intro d hd; cases hd)))
def cl_23596 : CNF.NClause := [(74,true),(2,true),(10,false),(6,false),(23,false),(19,false)]
theorem der_23596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23596 :=
  CNF.rup_sound cl_23596 [cl_770,cl_802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_770 v h) (hints_cons _ _ _ (inp_802 v h) (by intro d hd; cases hd)))
def cl_23597 : CNF.NClause := [(74,true),(23,true),(2,true),(10,false),(6,false),(29,false)]
theorem der_23597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23597 :=
  CNF.rup_sound cl_23597 [cl_786,cl_794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_786 v h) (hints_cons _ _ _ (inp_794 v h) (by intro d hd; cases hd)))
def cl_23598 : CNF.NClause := [(71,true),(26,false),(7,true),(13,false),(1,false),(19,false)]
theorem der_23598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23598 :=
  CNF.rup_sound cl_23598 [cl_595,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_595 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_23599 : CNF.NClause := [(71,true),(20,false),(7,true),(13,false),(1,false),(19,false)]
theorem der_23599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23599 :=
  CNF.rup_sound cl_23599 [cl_611,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_611 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_23600 : CNF.NClause := [(71,true),(20,false),(7,false),(1,false),(13,false),(19,false)]
theorem der_23600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23600 :=
  CNF.rup_sound cl_23600 [cl_609,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_609 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_23601 : CNF.NClause := [(85,true),(21,true),(12,true),(5,false),(3,false),(19,false)]
theorem der_23601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23601 :=
  CNF.rup_sound cl_23601 [cl_1525,cl_1493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1525 v h) (hints_cons _ _ _ (inp_1493 v h) (by intro d hd; cases hd)))
def cl_23602 : CNF.NClause := [(70,true),(3,false),(28,true),(6,false),(17,true),(14,true)]
theorem der_23602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23602 :=
  CNF.rup_sound cl_23602 [cl_573,cl_557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_573 v h) (hints_cons _ _ _ (inp_557 v h) (by intro d hd; cases hd)))
def cl_23603 : CNF.NClause := [(79,true),(15,true),(26,false),(8,false),(14,true),(21,false)]
theorem der_23603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23603 :=
  CNF.rup_sound cl_23603 [cl_1101,cl_23503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1101 v h) (hints_cons _ _ _ (der_23503 v h) (by intro d hd; cases hd)))
def cl_23604 : CNF.NClause := [(79,true),(15,true),(2,false),(26,false),(8,false),(14,true)]
theorem der_23604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23604 :=
  CNF.rup_sound cl_23604 [cl_1117,cl_23603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1117 v h) (hints_cons _ _ _ (der_23603 v h) (by intro d hd; cases hd)))
def cl_23605 : CNF.NClause := [(79,true),(14,true),(8,false),(2,false),(15,true),(21,false)]
theorem der_23605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23605 :=
  CNF.rup_sound cl_23605 [cl_1133,cl_23604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1133 v h) (hints_cons _ _ _ (der_23604 v h) (by intro d hd; cases hd)))
def cl_23606 : CNF.NClause := [(79,true),(15,true),(8,false),(2,false),(14,true),(21,true)]
theorem der_23606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23606 :=
  CNF.rup_sound cl_23606 [cl_1149,cl_23604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1149 v h) (hints_cons _ _ _ (der_23604 v h) (by intro d hd; cases hd)))
def cl_23607 : CNF.NClause := [(86,true),(14,true),(1,false),(5,false),(18,false),(29,false)]
theorem der_23607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23607 :=
  CNF.rup_sound cl_23607 [cl_1557,cl_1541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1557 v h) (hints_cons _ _ _ (inp_1541 v h) (by intro d hd; cases hd)))
def cl_23608 : CNF.NClause := [(86,true),(14,true),(1,false),(22,false),(5,false),(18,true)]
theorem der_23608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23608 :=
  CNF.rup_sound cl_23608 [cl_1549,cl_1581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1549 v h) (hints_cons _ _ _ (inp_1581 v h) (by intro d hd; cases hd)))
def cl_23609 : CNF.NClause := [(86,true),(18,true),(1,false),(14,true),(5,false),(22,true)]
theorem der_23609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23609 :=
  CNF.rup_sound cl_23609 [cl_1565,cl_23588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1565 v h) (hints_cons _ _ _ (der_23588 v h) (by intro d hd; cases hd)))
def cl_23610 : CNF.NClause := [(76,true),(24,false),(17,false),(1,false),(8,false),(10,false)]
theorem der_23610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23610 :=
  CNF.rup_sound cl_23610 [cl_897,cl_929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_897 v h) (hints_cons _ _ _ (inp_929 v h) (by intro d hd; cases hd)))
def cl_23611 : CNF.NClause := [(83,true),(17,false),(4,false),(11,false),(5,false),(23,false)]
theorem der_23611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23611 :=
  CNF.rup_sound cl_23611 [cl_1345,cl_23550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1345 v h) (hints_cons _ _ _ (der_23550 v h) (by intro d hd; cases hd)))
def cl_23612 : CNF.NClause := [(70,true),(20,false),(28,false),(6,false),(3,false),(17,false)]
theorem der_23612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23612 :=
  CNF.rup_sound cl_23612 [cl_517,cl_513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_517 v h) (hints_cons _ _ _ (inp_513 v h) (by intro d hd; cases hd)))
def cl_23613 : CNF.NClause := [(70,true),(28,true),(6,false),(3,false),(14,true),(20,false)]
theorem der_23613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23613 :=
  CNF.rup_sound cl_23613 [cl_549,cl_557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_549 v h) (hints_cons _ _ _ (inp_557 v h) (by intro d hd; cases hd)))
def cl_23614 : CNF.NClause := [(70,true),(28,true),(6,false),(3,false),(14,true),(20,true)]
theorem der_23614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23614 :=
  CNF.rup_sound cl_23614 [cl_565,cl_23602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_565 v h) (hints_cons _ _ _ (der_23602 v h) (by intro d hd; cases hd)))
def cl_23615 : CNF.NClause := [(84,true),(28,false),(2,true),(5,false),(16,false),(13,false)]
theorem der_23615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23615 :=
  CNF.rup_sound cl_23615 [cl_1426,cl_1410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1426 v h) (hints_cons _ _ _ (inp_1410 v h) (by intro d hd; cases hd)))
def cl_23616 : CNF.NClause := [(84,true),(28,false),(5,false),(24,false),(13,false),(16,false)]
theorem der_23616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23616 :=
  CNF.rup_sound cl_23616 [cl_1409,cl_1410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1409 v h) (hints_cons _ _ _ (inp_1410 v h) (by intro d hd; cases hd)))
def cl_23617 : CNF.NClause := [(84,true),(24,false),(2,true),(5,false),(13,false),(16,false)]
theorem der_23617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23617 :=
  CNF.rup_sound cl_23617 [cl_1442,cl_1410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1442 v h) (hints_cons _ _ _ (inp_1410 v h) (by intro d hd; cases hd)))
def cl_23618 : CNF.NClause := [(84,true),(28,true),(2,true),(5,false),(24,false),(13,false)]
theorem der_23618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23618 :=
  CNF.rup_sound cl_23618 [cl_1450,cl_23617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1450 v h) (hints_cons _ _ _ (der_23617 v h) (by intro d hd; cases hd)))
def cl_23619 : CNF.NClause := [(84,true),(16,false),(2,true),(13,false),(5,false),(24,true)]
theorem der_23619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23619 :=
  CNF.rup_sound cl_23619 [cl_1458,cl_23615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1458 v h) (hints_cons _ _ _ (der_23615 v h) (by intro d hd; cases hd)))
def cl_23620 : CNF.NClause := [(84,true),(16,true),(2,true),(13,false),(5,false),(28,true)]
theorem der_23620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23620 :=
  CNF.rup_sound cl_23620 [cl_1466,cl_23618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1466 v h) (hints_cons _ _ _ (der_23618 v h) (by intro d hd; cases hd)))
def cl_23621 : CNF.NClause := [(71,true),(20,false),(7,true),(19,false),(26,false),(13,false)]
theorem der_23621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23621 :=
  CNF.rup_sound cl_23621 [cl_580,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_580 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_23622 : CNF.NClause := [(71,true),(20,true),(13,false),(7,true),(26,false),(19,false)]
theorem der_23622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23622 :=
  CNF.rup_sound cl_23622 [cl_596,cl_23598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_596 v h) (hints_cons _ _ _ (der_23598 v h) (by intro d hd; cases hd)))
def cl_23623 : CNF.NClause := [(71,true),(20,false),(7,true),(13,false),(26,true),(19,false)]
theorem der_23623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23623 :=
  CNF.rup_sound cl_23623 [cl_612,cl_23599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_612 v h) (hints_cons _ _ _ (der_23599 v h) (by intro d hd; cases hd)))
def cl_23624 : CNF.NClause := [(71,true),(13,false),(7,true),(1,true),(26,true),(19,false)]
theorem der_23624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23624 :=
  CNF.rup_sound cl_23624 [cl_628,cl_23623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_628 v h) (hints_cons _ _ _ (der_23623 v h) (by intro d hd; cases hd)))
def cl_23625 : CNF.NClause := [(84,true),(28,false),(2,false),(5,false),(24,false),(13,false)]
theorem der_23625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23625 :=
  CNF.rup_sound cl_23625 [cl_1417,cl_23616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1417 v h) (hints_cons _ _ _ (der_23616 v h) (by intro d hd; cases hd)))
def cl_23626 : CNF.NClause := [(84,true),(28,false),(2,false),(5,false),(13,false),(16,true)]
theorem der_23626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23626 :=
  CNF.rup_sound cl_23626 [cl_1433,cl_23625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1433 v h) (hints_cons _ _ _ (der_23625 v h) (by intro d hd; cases hd)))
def cl_23627 : CNF.NClause := [(84,true),(16,true),(28,true),(13,false),(5,false),(24,false)]
theorem der_23627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23627 :=
  CNF.rup_sound cl_23627 [cl_1449,cl_23618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1449 v h) (hints_cons _ _ _ (der_23618 v h) (by intro d hd; cases hd)))
def cl_23628 : CNF.NClause := [(84,true),(16,true),(28,true),(13,false),(5,false),(24,true)]
theorem der_23628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23628 :=
  CNF.rup_sound cl_23628 [cl_1465,cl_23620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1465 v h) (hints_cons _ _ _ (der_23620 v h) (by intro d hd; cases hd)))
def cl_23629 : CNF.NClause := [(84,true),(24,false),(2,true),(5,false),(28,false),(13,false)]
theorem der_23629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23629 :=
  CNF.rup_sound cl_23629 [cl_1418,cl_1410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1418 v h) (hints_cons _ _ _ (inp_1410 v h) (by intro d hd; cases hd)))
def cl_23630 : CNF.NClause := [(84,true),(28,false),(2,true),(5,false),(13,false),(24,true)]
theorem der_23630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23630 :=
  CNF.rup_sound cl_23630 [cl_1434,cl_23615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1434 v h) (hints_cons _ _ _ (der_23615 v h) (by intro d hd; cases hd)))
def cl_23631 : CNF.NClause := [(71,true),(20,false),(7,false),(1,false),(19,true),(13,false)]
theorem der_23631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23631 :=
  CNF.rup_sound cl_23631 [cl_617,cl_23241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_617 v h) (hints_cons _ _ _ (der_23241 v h) (by intro d hd; cases hd)))
def cl_23632 : CNF.NClause := [(78,true),(15,false),(22,true),(4,false),(13,false),(6,false)]
theorem der_23632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23632 :=
  CNF.rup_sound cl_23632 [cl_1041,cl_1073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1041 v h) (hints_cons _ _ _ (inp_1073 v h) (by intro d hd; cases hd)))
def cl_23633 : CNF.NClause := [(81,true),(1,false),(23,false),(15,false),(9,false),(12,false)]
theorem der_23633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23633 :=
  CNF.rup_sound cl_23633 [cl_1217,cl_23551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1217 v h) (hints_cons _ _ _ (der_23551 v h) (by intro d hd; cases hd)))
def cl_23634 : CNF.NClause := [(75,true),(22,false),(9,false),(16,true),(10,false),(26,false)]
theorem der_23634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23634 :=
  CNF.rup_sound cl_23634 [cl_841,cl_842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_841 v h) (hints_cons _ _ _ (inp_842 v h) (by intro d hd; cases hd)))
def cl_23635 : CNF.NClause := [(69,true),(20,false),(9,false),(11,false),(18,true),(27,false)]
theorem der_23635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23635 :=
  CNF.rup_sound cl_23635 [cl_457,cl_23579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_457 v h) (hints_cons _ _ _ (der_23579 v h) (by intro d hd; cases hd)))
def cl_23636 : CNF.NClause := [(75,true),(10,false),(3,false),(9,false),(16,false),(26,false)]
theorem der_23636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23636 :=
  CNF.rup_sound cl_23636 [cl_849,cl_833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_849 v h) (hints_cons _ _ _ (inp_833 v h) (by intro d hd; cases hd)))
def cl_23637 : CNF.NClause := [(75,true),(10,false),(22,true),(16,true),(9,false),(26,false)]
theorem der_23637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23637 :=
  CNF.rup_sound cl_23637 [cl_857,cl_23555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_857 v h) (hints_cons _ _ _ (der_23555 v h) (by intro d hd; cases hd)))
def cl_23638 : CNF.NClause := [(79,true),(15,true),(2,true),(21,true),(14,false),(26,false)]
theorem der_23638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23638 :=
  CNF.rup_sound cl_23638 [cl_1116,cl_23506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1116 v h) (hints_cons _ _ _ (der_23506 v h) (by intro d hd; cases hd)))
def cl_23639 : CNF.NClause := [(79,true),(2,true),(21,true),(14,false),(15,false),(26,false)]
theorem der_23639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23639 :=
  CNF.rup_sound cl_23639 [cl_1108,cl_23504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1108 v h) (hints_cons _ _ _ (der_23504 v h) (by intro d hd; cases hd)))
def cl_23640 : CNF.NClause := [(79,true),(15,false),(2,true),(14,false),(26,true),(8,true)]
theorem der_23640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23640 :=
  CNF.rup_sound cl_23640 [cl_1140,cl_23571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1140 v h) (hints_cons _ _ _ (der_23571 v h) (by intro d hd; cases hd)))
def cl_23641 : CNF.NClause := [(79,true),(21,true),(26,true),(8,false),(15,false),(14,false)]
theorem der_23641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23641 :=
  CNF.rup_sound cl_23641 [cl_1137,cl_23512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1137 v h) (hints_cons _ _ _ (der_23512 v h) (by intro d hd; cases hd)))
def cl_23642 : CNF.NClause := [(85,false),(21,true),(12,true),(5,true),(3,true),(27,true)]
theorem der_23642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23642 :=
  CNF.rup_sound cl_23642 [cl_1536,cl_1528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1536 v h) (hints_cons _ _ _ (inp_1528 v h) (by intro d hd; cases hd)))
def cl_23643 : CNF.NClause := [(79,true),(15,false),(2,true),(21,true),(14,true),(26,false)]
theorem der_23643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23643 :=
  CNF.rup_sound cl_23643 [cl_1112,cl_23505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1112 v h) (hints_cons _ _ _ (der_23505 v h) (by intro d hd; cases hd)))
def cl_23644 : CNF.NClause := [(85,true),(12,true),(5,false),(21,true),(27,false),(3,false)]
theorem der_23644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23644 :=
  CNF.rup_sound cl_23644 [cl_1501,cl_1493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1501 v h) (hints_cons _ _ _ (inp_1493 v h) (by intro d hd; cases hd)))
def cl_23645 : CNF.NClause := [(85,true),(21,true),(27,true),(5,false),(3,false),(12,true)]
theorem der_23645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23645 :=
  CNF.rup_sound cl_23645 [cl_1533,cl_23601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1533 v h) (hints_cons _ _ _ (der_23601 v h) (by intro d hd; cases hd)))
def cl_23646 : CNF.NClause := [(73,true),(10,false),(4,false),(7,true),(18,false),(21,true)]
theorem der_23646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23646 :=
  CNF.rup_sound cl_23646 [cl_755,cl_23262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_755 v h) (hints_cons _ _ _ (der_23262 v h) (by intro d hd; cases hd)))
def cl_23647 : CNF.NClause := [(73,true),(21,true),(7,true),(18,false),(10,false),(28,false)]
theorem der_23647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23647 :=
  CNF.rup_sound cl_23647 [cl_724,cl_23262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_724 v h) (hints_cons _ _ _ (der_23262 v h) (by intro d hd; cases hd)))
def cl_23648 : CNF.NClause := [(85,true),(3,false),(27,false),(5,false),(19,false),(21,true)]
theorem der_23648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23648 :=
  CNF.rup_sound cl_23648 [cl_1489,cl_1493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1489 v h) (hints_cons _ _ _ (inp_1493 v h) (by intro d hd; cases hd)))
def cl_23649 : CNF.NClause := [(85,true),(27,true),(5,false),(3,false),(19,false),(21,true)]
theorem der_23649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23649 :=
  CNF.rup_sound cl_23649 [cl_1521,cl_23601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1521 v h) (hints_cons _ _ _ (der_23601 v h) (by intro d hd; cases hd)))
def cl_23650 : CNF.NClause := [(79,true),(26,false),(21,true),(8,false),(14,true),(15,false)]
theorem der_23650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23650 :=
  CNF.rup_sound cl_23650 [cl_1109,cl_23505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1109 v h) (hints_cons _ _ _ (der_23505 v h) (by intro d hd; cases hd)))
def cl_23651 : CNF.NClause := [(79,true),(14,true),(8,false),(2,false),(21,true),(15,false)]
theorem der_23651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23651 :=
  CNF.rup_sound cl_23651 [cl_1141,cl_23650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1141 v h) (hints_cons _ _ _ (der_23650 v h) (by intro d hd; cases hd)))
def cl_23652 : CNF.NClause := [(79,true),(26,false),(21,true),(8,false),(14,false),(15,false)]
theorem der_23652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23652 :=
  CNF.rup_sound cl_23652 [cl_1105,cl_23504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1105 v h) (hints_cons _ _ _ (der_23504 v h) (by intro d hd; cases hd)))
def cl_23653 : CNF.NClause := [(85,true),(3,false),(5,false),(21,true),(19,true),(27,false)]
theorem der_23653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23653 :=
  CNF.rup_sound cl_23653 [cl_1497,cl_23644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1497 v h) (hints_cons _ _ _ (der_23644 v h) (by intro d hd; cases hd)))
def cl_23654 : CNF.NClause := [(85,true),(5,false),(21,true),(3,false),(19,true),(27,true)]
theorem der_23654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23654 :=
  CNF.rup_sound cl_23654 [cl_1529,cl_23645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1529 v h) (hints_cons _ _ _ (der_23645 v h) (by intro d hd; cases hd)))
def cl_23656 : CNF.NClause := [(85,false),(27,true),(5,true),(12,true),(3,true),(19,true)]
theorem der_23656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23656 :=
  CNF.rup_sound cl_23656 [cl_1520,cl_23642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1520 v h) (hints_cons _ _ _ (der_23642 v h) (by intro d hd; cases hd)))
def cl_23657 : CNF.NClause := [(85,false),(5,true),(27,true),(21,true),(19,true),(3,true)]
theorem der_23657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23657 :=
  CNF.rup_sound cl_23657 [cl_1532,cl_23642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1532 v h) (hints_cons _ _ _ (der_23642 v h) (by intro d hd; cases hd)))
def cl_23658 : CNF.NClause := [(85,false),(27,true),(3,true),(12,true),(19,true),(21,true)]
theorem der_23658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23658 :=
  CNF.rup_sound cl_23658 [cl_1534,cl_23642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1534 v h) (hints_cons _ _ _ (der_23642 v h) (by intro d hd; cases hd)))
def cl_23659 : CNF.NClause := [(85,false),(21,true),(12,true),(19,true),(5,true),(27,true)]
theorem der_23659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23659 :=
  CNF.rup_sound cl_23659 [cl_1535,cl_23642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1535 v h) (hints_cons _ _ _ (der_23642 v h) (by intro d hd; cases hd)))
def cl_23660 : CNF.NClause := [(84,false),(16,true),(2,true),(13,true),(5,true),(24,true)]
theorem der_23660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23660 :=
  CNF.rup_sound cl_23660 [cl_1472,cl_1440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1472 v h) (hints_cons _ _ _ (inp_1440 v h) (by intro d hd; cases hd)))
def cl_23661 : CNF.NClause := [(83,false),(23,true),(26,true),(11,true),(4,true),(17,true)]
theorem der_23661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23661 :=
  CNF.rup_sound cl_23661 [cl_1408,cl_1406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1408 v h) (hints_cons _ _ _ (inp_1406 v h) (by intro d hd; cases hd)))
def cl_23663 : CNF.NClause := [(78,false),(13,true),(4,true),(6,true),(15,true),(22,true)]
theorem der_23663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23663 :=
  CNF.rup_sound cl_23663 [cl_1088,cl_1056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1088 v h) (hints_cons _ _ _ (inp_1056 v h) (by intro d hd; cases hd)))
def cl_23664 : CNF.NClause := [(76,false),(8,true),(24,true),(1,true),(10,true),(17,true)]
theorem der_23664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23664 :=
  CNF.rup_sound cl_23664 [cl_960,cl_928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_960 v h) (hints_cons _ _ _ (inp_928 v h) (by intro d hd; cases hd)))
def cl_23665 : CNF.NClause := [(74,false),(6,true),(2,true),(23,true),(10,true),(29,true)]
theorem der_23665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23665 :=
  CNF.rup_sound cl_23665 [cl_832,cl_824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_832 v h) (hints_cons _ _ _ (inp_824 v h) (by intro d hd; cases hd)))
def cl_23667 : CNF.NClause := [(68,false),(29,true),(12,true),(16,true),(8,true),(20,true)]
theorem der_23667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23667 :=
  CNF.rup_sound cl_23667 [cl_448,cl_447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_448 v h) (hints_cons _ _ _ (inp_447 v h) (by intro d hd; cases hd)))
def cl_23668 : CNF.NClause := [(56,false),(92,false),(65,false),(63,false),(64,false),(66,false)]
theorem der_23668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23668 :=
  CNF.rup_sound cl_23668 [cl_15490,cl_15489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15490 v h) (hints_cons _ _ _ (der_15489 v h) (by intro d hd; cases hd)))
def cl_23669 : CNF.NClause := [(56,false),(64,false),(65,false),(63,false),(66,false),(62,true)]
theorem der_23669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23669 :=
  CNF.rup_sound cl_23669 [cl_15522,cl_23668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15522 v h) (hints_cons _ _ _ (der_23668 v h) (by intro d hd; cases hd)))
def chunk002 : List CNF.NClause := [cl_23159,cl_23162,cl_23163,cl_23164,cl_23165,cl_23166,cl_23167,cl_23168,cl_23169,cl_23170,cl_23171,cl_23172,cl_23173,cl_23174,cl_23175,cl_23176,cl_23178,cl_23179,cl_23180,cl_23181,cl_23182,cl_23183,cl_23184,cl_23185,cl_23186,cl_23187,cl_23188,cl_23189,cl_23190,cl_23192,cl_23193,cl_23194,cl_23195,cl_23196,cl_23197,cl_23198,cl_23199,cl_23200,cl_23201,cl_23202,cl_23203,cl_23204,cl_23205,cl_23206,cl_23207,cl_23208,cl_23209,cl_23210,cl_23211,cl_23212,cl_23213,cl_23214,cl_23215,cl_23216,cl_23217,cl_23218,cl_23219,cl_23220,cl_23221,cl_23222,cl_23223,cl_23224,cl_23225,cl_23226,cl_23227,cl_23228,cl_23229,cl_23230,cl_23231,cl_23232,cl_23233,cl_23234,cl_23235,cl_23236,cl_23237,cl_23238,cl_23239,cl_23240,cl_23241,cl_23242,cl_23243,cl_23244,cl_23245,cl_23246,cl_23247,cl_23248,cl_23249,cl_23250,cl_23251,cl_23252,cl_23253,cl_23254,cl_23255,cl_23256,cl_23257,cl_23258,cl_23259,cl_23260,cl_23261,cl_23262,cl_23263,cl_23264,cl_23265,cl_23267,cl_23270,cl_23271,cl_23272,cl_23274,cl_23275,cl_23276,cl_23277,cl_23278,cl_23279,cl_23280,cl_23281,cl_23282,cl_23283,cl_23284,cl_23285,cl_23286,cl_23287,cl_23288,cl_23289,cl_23290,cl_23291,cl_23292,cl_23293,cl_23294,cl_23295,cl_23296,cl_23297,cl_23298,cl_23299,cl_23300,cl_23301,cl_23302,cl_23303,cl_23304,cl_23305,cl_23306,cl_23307,cl_23308,cl_23309,cl_23310,cl_23311,cl_23312,cl_23313,cl_23314,cl_23315,cl_23316,cl_23317,cl_23318,cl_23319,cl_23320,cl_23321,cl_23322,cl_23323,cl_23324,cl_23325,cl_23326,cl_23327,cl_23328,cl_23329,cl_23330,cl_23331,cl_23332,cl_23333,cl_23334,cl_23335,cl_23336,cl_23337,cl_23338,cl_23339,cl_23340,cl_23341,cl_23342,cl_23343,cl_23344,cl_23345,cl_23346,cl_23347,cl_23348,cl_23349,cl_23350,cl_23351,cl_23352,cl_23353,cl_23354,cl_23355,cl_23356,cl_23357,cl_23358,cl_23359,cl_23360,cl_23361,cl_23362,cl_23363,cl_23364,cl_23365,cl_23366,cl_23367,cl_23368,cl_23369,cl_23370,cl_23371,cl_23372,cl_23373,cl_23374,cl_23375,cl_23376,cl_23377,cl_23378,cl_23379,cl_23380,cl_23381,cl_23382,cl_23383,cl_23384,cl_23385,cl_23386,cl_23387,cl_23388,cl_23389,cl_23390,cl_23391,cl_23392,cl_23393,cl_23394,cl_23395,cl_23396,cl_23397,cl_23398,cl_23399,cl_23400,cl_23401,cl_23402,cl_23403,cl_23404,cl_23405,cl_23406,cl_23407,cl_23408,cl_23409,cl_23410,cl_23411,cl_23412,cl_23413,cl_23414,cl_23415,cl_23416,cl_23417,cl_23418,cl_23419,cl_23420,cl_23421,cl_23422,cl_23423,cl_23424,cl_23425,cl_23426,cl_23427,cl_23428,cl_23429,cl_23430,cl_23431,cl_23432,cl_23433,cl_23434,cl_23435,cl_23436,cl_23437,cl_23438,cl_23439,cl_23440,cl_23441,cl_23442,cl_23443,cl_23444,cl_23445,cl_23446,cl_23447,cl_23448,cl_23449,cl_23450,cl_23451,cl_23452,cl_23453,cl_23454,cl_23455,cl_23456,cl_23457,cl_23458,cl_23459,cl_23460,cl_23461,cl_23462,cl_23463,cl_23464,cl_23465,cl_23466,cl_23467,cl_23468,cl_23469,cl_23470,cl_23471,cl_23472,cl_23473,cl_23474,cl_23475,cl_23476,cl_23477,cl_23478,cl_23479,cl_23480,cl_23481,cl_23482,cl_23483,cl_23484,cl_23485,cl_23486,cl_23487,cl_23488,cl_23489,cl_23490,cl_23491,cl_23492,cl_23493,cl_23494,cl_23495,cl_23496,cl_23497,cl_23498,cl_23499,cl_23500,cl_23501,cl_23502,cl_23503,cl_23504,cl_23505,cl_23506,cl_23507,cl_23508,cl_23509,cl_23510,cl_23511,cl_23512,cl_23513,cl_23514,cl_23515,cl_23516,cl_23517,cl_23518,cl_23519,cl_23520,cl_23521,cl_23522,cl_23523,cl_23524,cl_23525,cl_23526,cl_23527,cl_23528,cl_23529,cl_23530,cl_23531,cl_23532,cl_23533,cl_23534,cl_23535,cl_23536,cl_23537,cl_23538,cl_23539,cl_23540,cl_23541,cl_23542,cl_23543,cl_23544,cl_23545,cl_23546,cl_23547,cl_23548,cl_23549,cl_23550,cl_23551,cl_23552,cl_23553,cl_23554,cl_23555,cl_23556,cl_23557,cl_23558,cl_23559,cl_23560,cl_23561,cl_23562,cl_23563,cl_23564,cl_23565,cl_23566,cl_23567,cl_23568,cl_23569,cl_23570,cl_23571,cl_23572,cl_23573,cl_23574,cl_23575,cl_23576,cl_23577,cl_23578,cl_23579,cl_23580,cl_23581,cl_23582,cl_23583,cl_23584,cl_23585,cl_23586,cl_23587,cl_23588,cl_23589,cl_23590,cl_23591,cl_23592,cl_23593,cl_23594,cl_23595,cl_23596,cl_23597,cl_23598,cl_23599,cl_23600,cl_23601,cl_23602,cl_23603,cl_23604,cl_23605,cl_23606,cl_23607,cl_23608,cl_23609,cl_23610,cl_23611,cl_23612,cl_23613,cl_23614,cl_23615,cl_23616,cl_23617,cl_23618,cl_23619,cl_23620,cl_23621,cl_23622,cl_23623,cl_23624,cl_23625,cl_23626,cl_23627,cl_23628,cl_23629,cl_23630,cl_23631,cl_23632,cl_23633,cl_23634,cl_23635,cl_23636,cl_23637,cl_23638,cl_23639,cl_23640,cl_23641,cl_23642,cl_23643,cl_23644,cl_23645,cl_23646,cl_23647,cl_23648,cl_23649,cl_23650,cl_23651,cl_23652,cl_23653,cl_23654,cl_23656,cl_23657,cl_23658,cl_23659,cl_23660,cl_23661,cl_23663,cl_23664,cl_23665,cl_23667,cl_23668,cl_23669]
theorem chunk_sound002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk002, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_23159 v h) (hints_cons _ _ _ (der_23162 v h) (hints_cons _ _ _ (der_23163 v h) (hints_cons _ _ _ (der_23164 v h) (hints_cons _ _ _ (der_23165 v h) (hints_cons _ _ _ (der_23166 v h) (hints_cons _ _ _ (der_23167 v h) (hints_cons _ _ _ (der_23168 v h) (hints_cons _ _ _ (der_23169 v h) (hints_cons _ _ _ (der_23170 v h) (hints_cons _ _ _ (der_23171 v h) (hints_cons _ _ _ (der_23172 v h) (hints_cons _ _ _ (der_23173 v h) (hints_cons _ _ _ (der_23174 v h) (hints_cons _ _ _ (der_23175 v h) (hints_cons _ _ _ (der_23176 v h) (hints_cons _ _ _ (der_23178 v h) (hints_cons _ _ _ (der_23179 v h) (hints_cons _ _ _ (der_23180 v h) (hints_cons _ _ _ (der_23181 v h) (hints_cons _ _ _ (der_23182 v h) (hints_cons _ _ _ (der_23183 v h) (hints_cons _ _ _ (der_23184 v h) (hints_cons _ _ _ (der_23185 v h) (hints_cons _ _ _ (der_23186 v h) (hints_cons _ _ _ (der_23187 v h) (hints_cons _ _ _ (der_23188 v h) (hints_cons _ _ _ (der_23189 v h) (hints_cons _ _ _ (der_23190 v h) (hints_cons _ _ _ (der_23192 v h) (hints_cons _ _ _ (der_23193 v h) (hints_cons _ _ _ (der_23194 v h) (hints_cons _ _ _ (der_23195 v h) (hints_cons _ _ _ (der_23196 v h) (hints_cons _ _ _ (der_23197 v h) (hints_cons _ _ _ (der_23198 v h) (hints_cons _ _ _ (der_23199 v h) (hints_cons _ _ _ (der_23200 v h) (hints_cons _ _ _ (der_23201 v h) (hints_cons _ _ _ (der_23202 v h) (hints_cons _ _ _ (der_23203 v h) (hints_cons _ _ _ (der_23204 v h) (hints_cons _ _ _ (der_23205 v h) (hints_cons _ _ _ (der_23206 v h) (hints_cons _ _ _ (der_23207 v h) (hints_cons _ _ _ (der_23208 v h) (hints_cons _ _ _ (der_23209 v h) (hints_cons _ _ _ (der_23210 v h) (hints_cons _ _ _ (der_23211 v h) (hints_cons _ _ _ (der_23212 v h) (hints_cons _ _ _ (der_23213 v h) (hints_cons _ _ _ (der_23214 v h) (hints_cons _ _ _ (der_23215 v h) (hints_cons _ _ _ (der_23216 v h) (hints_cons _ _ _ (der_23217 v h) (hints_cons _ _ _ (der_23218 v h) (hints_cons _ _ _ (der_23219 v h) (hints_cons _ _ _ (der_23220 v h) (hints_cons _ _ _ (der_23221 v h) (hints_cons _ _ _ (der_23222 v h) (hints_cons _ _ _ (der_23223 v h) (hints_cons _ _ _ (der_23224 v h) (hints_cons _ _ _ (der_23225 v h) (hints_cons _ _ _ (der_23226 v h) (hints_cons _ _ _ (der_23227 v h) (hints_cons _ _ _ (der_23228 v h) (hints_cons _ _ _ (der_23229 v h) (hints_cons _ _ _ (der_23230 v h) (hints_cons _ _ _ (der_23231 v h) (hints_cons _ _ _ (der_23232 v h) (hints_cons _ _ _ (der_23233 v h) (hints_cons _ _ _ (der_23234 v h) (hints_cons _ _ _ (der_23235 v h) (hints_cons _ _ _ (der_23236 v h) (hints_cons _ _ _ (der_23237 v h) (hints_cons _ _ _ (der_23238 v h) (hints_cons _ _ _ (der_23239 v h) (hints_cons _ _ _ (der_23240 v h) (hints_cons _ _ _ (der_23241 v h) (hints_cons _ _ _ (der_23242 v h) (hints_cons _ _ _ (der_23243 v h) (hints_cons _ _ _ (der_23244 v h) (hints_cons _ _ _ (der_23245 v h) (hints_cons _ _ _ (der_23246 v h) (hints_cons _ _ _ (der_23247 v h) (hints_cons _ _ _ (der_23248 v h) (hints_cons _ _ _ (der_23249 v h) (hints_cons _ _ _ (der_23250 v h) (hints_cons _ _ _ (der_23251 v h) (hints_cons _ _ _ (der_23252 v h) (hints_cons _ _ _ (der_23253 v h) (hints_cons _ _ _ (der_23254 v h) (hints_cons _ _ _ (der_23255 v h) (hints_cons _ _ _ (der_23256 v h) (hints_cons _ _ _ (der_23257 v h) (hints_cons _ _ _ (der_23258 v h) (hints_cons _ _ _ (der_23259 v h) (hints_cons _ _ _ (der_23260 v h) (hints_cons _ _ _ (der_23261 v h) (hints_cons _ _ _ (der_23262 v h) (hints_cons _ _ _ (der_23263 v h) (hints_cons _ _ _ (der_23264 v h) (hints_cons _ _ _ (der_23265 v h) (hints_cons _ _ _ (der_23267 v h) (hints_cons _ _ _ (der_23270 v h) (hints_cons _ _ _ (der_23271 v h) (hints_cons _ _ _ (der_23272 v h) (hints_cons _ _ _ (der_23274 v h) (hints_cons _ _ _ (der_23275 v h) (hints_cons _ _ _ (der_23276 v h) (hints_cons _ _ _ (der_23277 v h) (hints_cons _ _ _ (der_23278 v h) (hints_cons _ _ _ (der_23279 v h) (hints_cons _ _ _ (der_23280 v h) (hints_cons _ _ _ (der_23281 v h) (hints_cons _ _ _ (der_23282 v h) (hints_cons _ _ _ (der_23283 v h) (hints_cons _ _ _ (der_23284 v h) (hints_cons _ _ _ (der_23285 v h) (hints_cons _ _ _ (der_23286 v h) (hints_cons _ _ _ (der_23287 v h) (hints_cons _ _ _ (der_23288 v h) (hints_cons _ _ _ (der_23289 v h) (hints_cons _ _ _ (der_23290 v h) (hints_cons _ _ _ (der_23291 v h) (hints_cons _ _ _ (der_23292 v h) (hints_cons _ _ _ (der_23293 v h) (hints_cons _ _ _ (der_23294 v h) (hints_cons _ _ _ (der_23295 v h) (hints_cons _ _ _ (der_23296 v h) (hints_cons _ _ _ (der_23297 v h) (hints_cons _ _ _ (der_23298 v h) (hints_cons _ _ _ (der_23299 v h) (hints_cons _ _ _ (der_23300 v h) (hints_cons _ _ _ (der_23301 v h) (hints_cons _ _ _ (der_23302 v h) (hints_cons _ _ _ (der_23303 v h) (hints_cons _ _ _ (der_23304 v h) (hints_cons _ _ _ (der_23305 v h) (hints_cons _ _ _ (der_23306 v h) (hints_cons _ _ _ (der_23307 v h) (hints_cons _ _ _ (der_23308 v h) (hints_cons _ _ _ (der_23309 v h) (hints_cons _ _ _ (der_23310 v h) (hints_cons _ _ _ (der_23311 v h) (hints_cons _ _ _ (der_23312 v h) (hints_cons _ _ _ (der_23313 v h) (hints_cons _ _ _ (der_23314 v h) (hints_cons _ _ _ (der_23315 v h) (hints_cons _ _ _ (der_23316 v h) (hints_cons _ _ _ (der_23317 v h) (hints_cons _ _ _ (der_23318 v h) (hints_cons _ _ _ (der_23319 v h) (hints_cons _ _ _ (der_23320 v h) (hints_cons _ _ _ (der_23321 v h) (hints_cons _ _ _ (der_23322 v h) (hints_cons _ _ _ (der_23323 v h) (hints_cons _ _ _ (der_23324 v h) (hints_cons _ _ _ (der_23325 v h) (hints_cons _ _ _ (der_23326 v h) (hints_cons _ _ _ (der_23327 v h) (hints_cons _ _ _ (der_23328 v h) (hints_cons _ _ _ (der_23329 v h) (hints_cons _ _ _ (der_23330 v h) (hints_cons _ _ _ (der_23331 v h) (hints_cons _ _ _ (der_23332 v h) (hints_cons _ _ _ (der_23333 v h) (hints_cons _ _ _ (der_23334 v h) (hints_cons _ _ _ (der_23335 v h) (hints_cons _ _ _ (der_23336 v h) (hints_cons _ _ _ (der_23337 v h) (hints_cons _ _ _ (der_23338 v h) (hints_cons _ _ _ (der_23339 v h) (hints_cons _ _ _ (der_23340 v h) (hints_cons _ _ _ (der_23341 v h) (hints_cons _ _ _ (der_23342 v h) (hints_cons _ _ _ (der_23343 v h) (hints_cons _ _ _ (der_23344 v h) (hints_cons _ _ _ (der_23345 v h) (hints_cons _ _ _ (der_23346 v h) (hints_cons _ _ _ (der_23347 v h) (hints_cons _ _ _ (der_23348 v h) (hints_cons _ _ _ (der_23349 v h) (hints_cons _ _ _ (der_23350 v h) (hints_cons _ _ _ (der_23351 v h) (hints_cons _ _ _ (der_23352 v h) (hints_cons _ _ _ (der_23353 v h) (hints_cons _ _ _ (der_23354 v h) (hints_cons _ _ _ (der_23355 v h) (hints_cons _ _ _ (der_23356 v h) (hints_cons _ _ _ (der_23357 v h) (hints_cons _ _ _ (der_23358 v h) (hints_cons _ _ _ (der_23359 v h) (hints_cons _ _ _ (der_23360 v h) (hints_cons _ _ _ (der_23361 v h) (hints_cons _ _ _ (der_23362 v h) (hints_cons _ _ _ (der_23363 v h) (hints_cons _ _ _ (der_23364 v h) (hints_cons _ _ _ (der_23365 v h) (hints_cons _ _ _ (der_23366 v h) (hints_cons _ _ _ (der_23367 v h) (hints_cons _ _ _ (der_23368 v h) (hints_cons _ _ _ (der_23369 v h) (hints_cons _ _ _ (der_23370 v h) (hints_cons _ _ _ (der_23371 v h) (hints_cons _ _ _ (der_23372 v h) (hints_cons _ _ _ (der_23373 v h) (hints_cons _ _ _ (der_23374 v h) (hints_cons _ _ _ (der_23375 v h) (hints_cons _ _ _ (der_23376 v h) (hints_cons _ _ _ (der_23377 v h) (hints_cons _ _ _ (der_23378 v h) (hints_cons _ _ _ (der_23379 v h) (hints_cons _ _ _ (der_23380 v h) (hints_cons _ _ _ (der_23381 v h) (hints_cons _ _ _ (der_23382 v h) (hints_cons _ _ _ (der_23383 v h) (hints_cons _ _ _ (der_23384 v h) (hints_cons _ _ _ (der_23385 v h) (hints_cons _ _ _ (der_23386 v h) (hints_cons _ _ _ (der_23387 v h) (hints_cons _ _ _ (der_23388 v h) (hints_cons _ _ _ (der_23389 v h) (hints_cons _ _ _ (der_23390 v h) (hints_cons _ _ _ (der_23391 v h) (hints_cons _ _ _ (der_23392 v h) (hints_cons _ _ _ (der_23393 v h) (hints_cons _ _ _ (der_23394 v h) (hints_cons _ _ _ (der_23395 v h) (hints_cons _ _ _ (der_23396 v h) (hints_cons _ _ _ (der_23397 v h) (hints_cons _ _ _ (der_23398 v h) (hints_cons _ _ _ (der_23399 v h) (hints_cons _ _ _ (der_23400 v h) (hints_cons _ _ _ (der_23401 v h) (hints_cons _ _ _ (der_23402 v h) (hints_cons _ _ _ (der_23403 v h) (hints_cons _ _ _ (der_23404 v h) (hints_cons _ _ _ (der_23405 v h) (hints_cons _ _ _ (der_23406 v h) (hints_cons _ _ _ (der_23407 v h) (hints_cons _ _ _ (der_23408 v h) (hints_cons _ _ _ (der_23409 v h) (hints_cons _ _ _ (der_23410 v h) (hints_cons _ _ _ (der_23411 v h) (hints_cons _ _ _ (der_23412 v h) (hints_cons _ _ _ (der_23413 v h) (hints_cons _ _ _ (der_23414 v h) (hints_cons _ _ _ (der_23415 v h) (hints_cons _ _ _ (der_23416 v h) (hints_cons _ _ _ (der_23417 v h) (hints_cons _ _ _ (der_23418 v h) (hints_cons _ _ _ (der_23419 v h) (hints_cons _ _ _ (der_23420 v h) (hints_cons _ _ _ (der_23421 v h) (hints_cons _ _ _ (der_23422 v h) (hints_cons _ _ _ (der_23423 v h) (hints_cons _ _ _ (der_23424 v h) (hints_cons _ _ _ (der_23425 v h) (hints_cons _ _ _ (der_23426 v h) (hints_cons _ _ _ (der_23427 v h) (hints_cons _ _ _ (der_23428 v h) (hints_cons _ _ _ (der_23429 v h) (hints_cons _ _ _ (der_23430 v h) (hints_cons _ _ _ (der_23431 v h) (hints_cons _ _ _ (der_23432 v h) (hints_cons _ _ _ (der_23433 v h) (hints_cons _ _ _ (der_23434 v h) (hints_cons _ _ _ (der_23435 v h) (hints_cons _ _ _ (der_23436 v h) (hints_cons _ _ _ (der_23437 v h) (hints_cons _ _ _ (der_23438 v h) (hints_cons _ _ _ (der_23439 v h) (hints_cons _ _ _ (der_23440 v h) (hints_cons _ _ _ (der_23441 v h) (hints_cons _ _ _ (der_23442 v h) (hints_cons _ _ _ (der_23443 v h) (hints_cons _ _ _ (der_23444 v h) (hints_cons _ _ _ (der_23445 v h) (hints_cons _ _ _ (der_23446 v h) (hints_cons _ _ _ (der_23447 v h) (hints_cons _ _ _ (der_23448 v h) (hints_cons _ _ _ (der_23449 v h) (hints_cons _ _ _ (der_23450 v h) (hints_cons _ _ _ (der_23451 v h) (hints_cons _ _ _ (der_23452 v h) (hints_cons _ _ _ (der_23453 v h) (hints_cons _ _ _ (der_23454 v h) (hints_cons _ _ _ (der_23455 v h) (hints_cons _ _ _ (der_23456 v h) (hints_cons _ _ _ (der_23457 v h) (hints_cons _ _ _ (der_23458 v h) (hints_cons _ _ _ (der_23459 v h) (hints_cons _ _ _ (der_23460 v h) (hints_cons _ _ _ (der_23461 v h) (hints_cons _ _ _ (der_23462 v h) (hints_cons _ _ _ (der_23463 v h) (hints_cons _ _ _ (der_23464 v h) (hints_cons _ _ _ (der_23465 v h) (hints_cons _ _ _ (der_23466 v h) (hints_cons _ _ _ (der_23467 v h) (hints_cons _ _ _ (der_23468 v h) (hints_cons _ _ _ (der_23469 v h) (hints_cons _ _ _ (der_23470 v h) (hints_cons _ _ _ (der_23471 v h) (hints_cons _ _ _ (der_23472 v h) (hints_cons _ _ _ (der_23473 v h) (hints_cons _ _ _ (der_23474 v h) (hints_cons _ _ _ (der_23475 v h) (hints_cons _ _ _ (der_23476 v h) (hints_cons _ _ _ (der_23477 v h) (hints_cons _ _ _ (der_23478 v h) (hints_cons _ _ _ (der_23479 v h) (hints_cons _ _ _ (der_23480 v h) (hints_cons _ _ _ (der_23481 v h) (hints_cons _ _ _ (der_23482 v h) (hints_cons _ _ _ (der_23483 v h) (hints_cons _ _ _ (der_23484 v h) (hints_cons _ _ _ (der_23485 v h) (hints_cons _ _ _ (der_23486 v h) (hints_cons _ _ _ (der_23487 v h) (hints_cons _ _ _ (der_23488 v h) (hints_cons _ _ _ (der_23489 v h) (hints_cons _ _ _ (der_23490 v h) (hints_cons _ _ _ (der_23491 v h) (hints_cons _ _ _ (der_23492 v h) (hints_cons _ _ _ (der_23493 v h) (hints_cons _ _ _ (der_23494 v h) (hints_cons _ _ _ (der_23495 v h) (hints_cons _ _ _ (der_23496 v h) (hints_cons _ _ _ (der_23497 v h) (hints_cons _ _ _ (der_23498 v h) (hints_cons _ _ _ (der_23499 v h) (hints_cons _ _ _ (der_23500 v h) (hints_cons _ _ _ (der_23501 v h) (hints_cons _ _ _ (der_23502 v h) (hints_cons _ _ _ (der_23503 v h) (hints_cons _ _ _ (der_23504 v h) (hints_cons _ _ _ (der_23505 v h) (hints_cons _ _ _ (der_23506 v h) (hints_cons _ _ _ (der_23507 v h) (hints_cons _ _ _ (der_23508 v h) (hints_cons _ _ _ (der_23509 v h) (hints_cons _ _ _ (der_23510 v h) (hints_cons _ _ _ (der_23511 v h) (hints_cons _ _ _ (der_23512 v h) (hints_cons _ _ _ (der_23513 v h) (hints_cons _ _ _ (der_23514 v h) (hints_cons _ _ _ (der_23515 v h) (hints_cons _ _ _ (der_23516 v h) (hints_cons _ _ _ (der_23517 v h) (hints_cons _ _ _ (der_23518 v h) (hints_cons _ _ _ (der_23519 v h) (hints_cons _ _ _ (der_23520 v h) (hints_cons _ _ _ (der_23521 v h) (hints_cons _ _ _ (der_23522 v h) (hints_cons _ _ _ (der_23523 v h) (hints_cons _ _ _ (der_23524 v h) (hints_cons _ _ _ (der_23525 v h) (hints_cons _ _ _ (der_23526 v h) (hints_cons _ _ _ (der_23527 v h) (hints_cons _ _ _ (der_23528 v h) (hints_cons _ _ _ (der_23529 v h) (hints_cons _ _ _ (der_23530 v h) (hints_cons _ _ _ (der_23531 v h) (hints_cons _ _ _ (der_23532 v h) (hints_cons _ _ _ (der_23533 v h) (hints_cons _ _ _ (der_23534 v h) (hints_cons _ _ _ (der_23535 v h) (hints_cons _ _ _ (der_23536 v h) (hints_cons _ _ _ (der_23537 v h) (hints_cons _ _ _ (der_23538 v h) (hints_cons _ _ _ (der_23539 v h) (hints_cons _ _ _ (der_23540 v h) (hints_cons _ _ _ (der_23541 v h) (hints_cons _ _ _ (der_23542 v h) (hints_cons _ _ _ (der_23543 v h) (hints_cons _ _ _ (der_23544 v h) (hints_cons _ _ _ (der_23545 v h) (hints_cons _ _ _ (der_23546 v h) (hints_cons _ _ _ (der_23547 v h) (hints_cons _ _ _ (der_23548 v h) (hints_cons _ _ _ (der_23549 v h) (hints_cons _ _ _ (der_23550 v h) (hints_cons _ _ _ (der_23551 v h) (hints_cons _ _ _ (der_23552 v h) (hints_cons _ _ _ (der_23553 v h) (hints_cons _ _ _ (der_23554 v h) (hints_cons _ _ _ (der_23555 v h) (hints_cons _ _ _ (der_23556 v h) (hints_cons _ _ _ (der_23557 v h) (hints_cons _ _ _ (der_23558 v h) (hints_cons _ _ _ (der_23559 v h) (hints_cons _ _ _ (der_23560 v h) (hints_cons _ _ _ (der_23561 v h) (hints_cons _ _ _ (der_23562 v h) (hints_cons _ _ _ (der_23563 v h) (hints_cons _ _ _ (der_23564 v h) (hints_cons _ _ _ (der_23565 v h) (hints_cons _ _ _ (der_23566 v h) (hints_cons _ _ _ (der_23567 v h) (hints_cons _ _ _ (der_23568 v h) (hints_cons _ _ _ (der_23569 v h) (hints_cons _ _ _ (der_23570 v h) (hints_cons _ _ _ (der_23571 v h) (hints_cons _ _ _ (der_23572 v h) (hints_cons _ _ _ (der_23573 v h) (hints_cons _ _ _ (der_23574 v h) (hints_cons _ _ _ (der_23575 v h) (hints_cons _ _ _ (der_23576 v h) (hints_cons _ _ _ (der_23577 v h) (hints_cons _ _ _ (der_23578 v h) (hints_cons _ _ _ (der_23579 v h) (hints_cons _ _ _ (der_23580 v h) (hints_cons _ _ _ (der_23581 v h) (hints_cons _ _ _ (der_23582 v h) (hints_cons _ _ _ (der_23583 v h) (hints_cons _ _ _ (der_23584 v h) (hints_cons _ _ _ (der_23585 v h) (hints_cons _ _ _ (der_23586 v h) (hints_cons _ _ _ (der_23587 v h) (hints_cons _ _ _ (der_23588 v h) (hints_cons _ _ _ (der_23589 v h) (hints_cons _ _ _ (der_23590 v h) (hints_cons _ _ _ (der_23591 v h) (hints_cons _ _ _ (der_23592 v h) (hints_cons _ _ _ (der_23593 v h) (hints_cons _ _ _ (der_23594 v h) (hints_cons _ _ _ (der_23595 v h) (hints_cons _ _ _ (der_23596 v h) (hints_cons _ _ _ (der_23597 v h) (hints_cons _ _ _ (der_23598 v h) (hints_cons _ _ _ (der_23599 v h) (hints_cons _ _ _ (der_23600 v h) (hints_cons _ _ _ (der_23601 v h) (hints_cons _ _ _ (der_23602 v h) (hints_cons _ _ _ (der_23603 v h) (hints_cons _ _ _ (der_23604 v h) (hints_cons _ _ _ (der_23605 v h) (hints_cons _ _ _ (der_23606 v h) (hints_cons _ _ _ (der_23607 v h) (hints_cons _ _ _ (der_23608 v h) (hints_cons _ _ _ (der_23609 v h) (hints_cons _ _ _ (der_23610 v h) (hints_cons _ _ _ (der_23611 v h) (hints_cons _ _ _ (der_23612 v h) (hints_cons _ _ _ (der_23613 v h) (hints_cons _ _ _ (der_23614 v h) (hints_cons _ _ _ (der_23615 v h) (hints_cons _ _ _ (der_23616 v h) (hints_cons _ _ _ (der_23617 v h) (hints_cons _ _ _ (der_23618 v h) (hints_cons _ _ _ (der_23619 v h) (hints_cons _ _ _ (der_23620 v h) (hints_cons _ _ _ (der_23621 v h) (hints_cons _ _ _ (der_23622 v h) (hints_cons _ _ _ (der_23623 v h) (hints_cons _ _ _ (der_23624 v h) (hints_cons _ _ _ (der_23625 v h) (hints_cons _ _ _ (der_23626 v h) (hints_cons _ _ _ (der_23627 v h) (hints_cons _ _ _ (der_23628 v h) (hints_cons _ _ _ (der_23629 v h) (hints_cons _ _ _ (der_23630 v h) (hints_cons _ _ _ (der_23631 v h) (hints_cons _ _ _ (der_23632 v h) (hints_cons _ _ _ (der_23633 v h) (hints_cons _ _ _ (der_23634 v h) (hints_cons _ _ _ (der_23635 v h) (hints_cons _ _ _ (der_23636 v h) (hints_cons _ _ _ (der_23637 v h) (hints_cons _ _ _ (der_23638 v h) (hints_cons _ _ _ (der_23639 v h) (hints_cons _ _ _ (der_23640 v h) (hints_cons _ _ _ (der_23641 v h) (hints_cons _ _ _ (der_23642 v h) (hints_cons _ _ _ (der_23643 v h) (hints_cons _ _ _ (der_23644 v h) (hints_cons _ _ _ (der_23645 v h) (hints_cons _ _ _ (der_23646 v h) (hints_cons _ _ _ (der_23647 v h) (hints_cons _ _ _ (der_23648 v h) (hints_cons _ _ _ (der_23649 v h) (hints_cons _ _ _ (der_23650 v h) (hints_cons _ _ _ (der_23651 v h) (hints_cons _ _ _ (der_23652 v h) (hints_cons _ _ _ (der_23653 v h) (hints_cons _ _ _ (der_23654 v h) (hints_cons _ _ _ (der_23656 v h) (hints_cons _ _ _ (der_23657 v h) (hints_cons _ _ _ (der_23658 v h) (hints_cons _ _ _ (der_23659 v h) (hints_cons _ _ _ (der_23660 v h) (hints_cons _ _ _ (der_23661 v h) (hints_cons _ _ _ (der_23663 v h) (hints_cons _ _ _ (der_23664 v h) (hints_cons _ _ _ (der_23665 v h) (hints_cons _ _ _ (der_23667 v h) (hints_cons _ _ _ (der_23668 v h) (hints_cons _ _ _ (der_23669 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix002 := prefix001 ++ chunk002
theorem prefix_sound002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix002, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound001 v h c hc
  · exact chunk_sound002 v h c hc
end Percolation.NReplay
