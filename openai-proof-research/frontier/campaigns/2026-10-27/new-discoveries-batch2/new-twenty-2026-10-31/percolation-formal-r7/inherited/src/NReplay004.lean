import NReplay003
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_24178 : CNF.NClause := [(71,true),(13,false),(26,true),(7,false),(1,false),(19,false)]
theorem der_24178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24178 :=
  CNF.rup_sound cl_24178 [cl_625,cl_23600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_625 v h) (hints_cons _ _ _ (der_23600 v h) (by intro d hd; cases hd)))
def cl_24179 : CNF.NClause := [(68,true),(20,true),(4,false),(12,true),(16,false),(29,false)]
theorem der_24179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24179 :=
  CNF.rup_sound cl_24179 [cl_407,cl_23516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_407 v h) (hints_cons _ _ _ (der_23516 v h) (by intro d hd; cases hd)))
def cl_24180 : CNF.NClause := [(68,true),(29,true),(4,false),(8,true),(20,true),(16,false)]
theorem der_24180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24180 :=
  CNF.rup_sound cl_24180 [cl_439,cl_24168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_439 v h) (hints_cons _ _ _ (der_24168 v h) (by intro d hd; cases hd)))
def cl_24181 : CNF.NClause := [(68,true),(29,false),(4,true),(8,true),(16,false),(20,true)]
theorem der_24181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24181 :=
  CNF.rup_sound cl_24181 [cl_408,cl_23985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_408 v h) (hints_cons _ _ _ (der_23985 v h) (by intro d hd; cases hd)))
def cl_24182 : CNF.NClause := [(69,true),(9,true),(11,false),(2,true),(27,false),(20,true)]
theorem der_24182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24182 :=
  CNF.rup_sound cl_24182 [cl_468,cl_23586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_468 v h) (hints_cons _ _ _ (der_23586 v h) (by intro d hd; cases hd)))
def cl_24183 : CNF.NClause := [(71,true),(26,false),(13,false),(7,false),(19,true),(1,false)]
theorem der_24183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24183 :=
  CNF.rup_sound cl_24183 [cl_601,cl_23241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_601 v h) (hints_cons _ _ _ (der_23241 v h) (by intro d hd; cases hd)))
def cl_24184 : CNF.NClause := [(71,true),(13,false),(1,false),(7,false),(19,true),(20,true)]
theorem der_24184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24184 :=
  CNF.rup_sound cl_24184 [cl_633,cl_24183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_633 v h) (hints_cons _ _ _ (der_24183 v h) (by intro d hd; cases hd)))
def cl_24185 : CNF.NClause := [(71,true),(20,true),(7,true),(1,true),(13,false),(26,false)]
theorem der_24185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24185 :=
  CNF.rup_sound cl_24185 [cl_604,cl_23622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_604 v h) (hints_cons _ _ _ (der_23622 v h) (by intro d hd; cases hd)))
def cl_24186 : CNF.NClause := [(69,true),(2,true),(11,false),(18,false),(20,true),(27,true)]
theorem der_24186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24186 :=
  CNF.rup_sound cl_24186 [cl_500,cl_24174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_500 v h) (hints_cons _ _ _ (der_24174 v h) (by intro d hd; cases hd)))
def cl_24187 : CNF.NClause := [(70,true),(17,false),(28,false),(3,false),(14,true),(6,false)]
theorem der_24187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24187 :=
  CNF.rup_sound cl_24187 [cl_533,cl_23612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_533 v h) (hints_cons _ _ _ (der_23612 v h) (by intro d hd; cases hd)))
def cl_24188 : CNF.NClause := [(71,true),(1,false),(7,true),(13,false),(19,true),(26,false)]
theorem der_24188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24188 :=
  CNF.rup_sound cl_24188 [cl_603,cl_23241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_603 v h) (hints_cons _ _ _ (der_23241 v h) (by intro d hd; cases hd)))
def cl_24189 : CNF.NClause := [(86,true),(29,false),(14,false),(22,false),(5,true),(18,false)]
theorem der_24189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24189 :=
  CNF.rup_sound cl_24189 [cl_1540,cl_1539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1540 v h) (hints_cons _ _ _ (inp_1539 v h) (by intro d hd; cases hd)))
def cl_24190 : CNF.NClause := [(81,true),(1,true),(9,false),(12,false),(15,false),(23,false)]
theorem der_24190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24190 :=
  CNF.rup_sound cl_24190 [cl_1218,cl_1250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1218 v h) (hints_cons _ _ _ (inp_1250 v h) (by intro d hd; cases hd)))
def cl_24191 : CNF.NClause := [(76,true),(8,true),(17,false),(1,true),(24,false),(27,false)]
theorem der_24191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24191 :=
  CNF.rup_sound cl_24191 [cl_904,cl_900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_904 v h) (hints_cons _ _ _ (inp_900 v h) (by intro d hd; cases hd)))
def cl_24192 : CNF.NClause := [(76,true),(27,false),(10,false),(17,false),(1,true),(24,false)]
theorem der_24192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24192 :=
  CNF.rup_sound cl_24192 [cl_898,cl_900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_898 v h) (hints_cons _ _ _ (inp_900 v h) (by intro d hd; cases hd)))
def cl_24193 : CNF.NClause := [(76,true),(27,false),(8,false),(17,false),(1,true),(24,false)]
theorem der_24193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24193 :=
  CNF.rup_sound cl_24193 [cl_902,cl_24192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_902 v h) (hints_cons _ _ _ (der_24192 v h) (by intro d hd; cases hd)))
def cl_24194 : CNF.NClause := [(76,true),(27,false),(8,false),(10,false),(1,true),(24,false)]
theorem der_24194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24194 :=
  CNF.rup_sound cl_24194 [cl_906,cl_24192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_906 v h) (hints_cons _ _ _ (der_24192 v h) (by intro d hd; cases hd)))
def cl_24195 : CNF.NClause := [(76,true),(27,false),(8,false),(17,true),(1,true),(24,false)]
theorem der_24195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24195 :=
  CNF.rup_sound cl_24195 [cl_910,cl_24194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_910 v h) (hints_cons _ _ _ (der_24194 v h) (by intro d hd; cases hd)))
def cl_24196 : CNF.NClause := [(76,true),(10,false),(8,false),(1,true),(17,false),(27,false)]
theorem der_24196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24196 :=
  CNF.rup_sound cl_24196 [cl_914,cl_24192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_914 v h) (hints_cons _ _ _ (der_24192 v h) (by intro d hd; cases hd)))
def cl_24197 : CNF.NClause := [(76,true),(27,false),(8,false),(10,true),(17,false),(1,true)]
theorem der_24197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24197 :=
  CNF.rup_sound cl_24197 [cl_918,cl_24193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_918 v h) (hints_cons _ _ _ (der_24193 v h) (by intro d hd; cases hd)))
def cl_24198 : CNF.NClause := [(76,true),(10,false),(8,false),(1,true),(17,true),(27,false)]
theorem der_24198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24198 :=
  CNF.rup_sound cl_24198 [cl_922,cl_24194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_922 v h) (hints_cons _ _ _ (der_24194 v h) (by intro d hd; cases hd)))
def cl_24199 : CNF.NClause := [(76,true),(27,false),(8,false),(17,true),(24,true),(1,true)]
theorem der_24199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24199 :=
  CNF.rup_sound cl_24199 [cl_926,cl_24198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_926 v h) (hints_cons _ _ _ (der_24198 v h) (by intro d hd; cases hd)))
def cl_24200 : CNF.NClause := [(76,true),(27,true),(10,false),(17,false),(1,true),(24,false)]
theorem der_24200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24200 :=
  CNF.rup_sound cl_24200 [cl_930,cl_23594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_930 v h) (hints_cons _ _ _ (der_23594 v h) (by intro d hd; cases hd)))
def cl_24201 : CNF.NClause := [(76,true),(27,true),(8,false),(17,false),(1,true),(24,false)]
theorem der_24201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24201 :=
  CNF.rup_sound cl_24201 [cl_934,cl_24200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_934 v h) (hints_cons _ _ _ (der_24200 v h) (by intro d hd; cases hd)))
def cl_24202 : CNF.NClause := [(76,true),(8,false),(10,false),(17,true),(1,true),(24,false)]
theorem der_24202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24202 :=
  CNF.rup_sound cl_24202 [cl_938,cl_24194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_938 v h) (hints_cons _ _ _ (der_24194 v h) (by intro d hd; cases hd)))
def cl_24203 : CNF.NClause := [(76,true),(8,false),(10,true),(17,true),(1,true),(24,false)]
theorem der_24203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24203 :=
  CNF.rup_sound cl_24203 [cl_942,cl_24195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_942 v h) (hints_cons _ _ _ (der_24195 v h) (by intro d hd; cases hd)))
def cl_24204 : CNF.NClause := [(76,true),(10,false),(8,false),(1,true),(17,false),(27,true)]
theorem der_24204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24204 :=
  CNF.rup_sound cl_24204 [cl_946,cl_24200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_946 v h) (hints_cons _ _ _ (der_24200 v h) (by intro d hd; cases hd)))
def cl_24205 : CNF.NClause := [(76,true),(17,false),(27,true),(8,false),(24,true),(1,true)]
theorem der_24205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24205 :=
  CNF.rup_sound cl_24205 [cl_950,cl_24204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_950 v h) (hints_cons _ _ _ (der_24204 v h) (by intro d hd; cases hd)))
def cl_24206 : CNF.NClause := [(76,true),(10,false),(8,false),(1,true),(17,true),(24,true)]
theorem der_24206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24206 :=
  CNF.rup_sound cl_24206 [cl_954,cl_24198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_954 v h) (hints_cons _ _ _ (der_24198 v h) (by intro d hd; cases hd)))
def cl_24207 : CNF.NClause := [(71,true),(20,false),(7,false),(13,false),(19,false),(26,false)]
theorem der_24207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24207 :=
  CNF.rup_sound cl_24207 [cl_578,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_578 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_24208 : CNF.NClause := [(71,true),(20,false),(7,false),(13,true),(19,false),(26,false)]
theorem der_24208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24208 :=
  CNF.rup_sound cl_24208 [cl_582,cl_23466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_582 v h) (hints_cons _ _ _ (der_23466 v h) (by intro d hd; cases hd)))
def cl_24209 : CNF.NClause := [(71,true),(20,false),(7,false),(13,false),(19,true),(26,false)]
theorem der_24209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24209 :=
  CNF.rup_sound cl_24209 [cl_586,cl_23241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_586 v h) (hints_cons _ _ _ (der_23241 v h) (by intro d hd; cases hd)))
def cl_24210 : CNF.NClause := [(71,true),(20,false),(7,false),(13,true),(19,true),(26,false)]
theorem der_24210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24210 :=
  CNF.rup_sound cl_24210 [cl_590,cl_23465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_590 v h) (hints_cons _ _ _ (der_23465 v h) (by intro d hd; cases hd)))
def cl_24211 : CNF.NClause := [(71,true),(26,false),(7,false),(13,false),(20,true),(19,false)]
theorem der_24211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24211 :=
  CNF.rup_sound cl_24211 [cl_594,cl_24177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_594 v h) (hints_cons _ _ _ (der_24177 v h) (by intro d hd; cases hd)))
def cl_24212 : CNF.NClause := [(71,true),(26,false),(7,false),(1,true),(20,true),(19,false)]
theorem der_24212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24212 :=
  CNF.rup_sound cl_24212 [cl_598,cl_24211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_598 v h) (hints_cons _ _ _ (der_24211 v h) (by intro d hd; cases hd)))
def cl_24213 : CNF.NClause := [(71,true),(26,false),(7,false),(1,true),(19,true),(13,false)]
theorem der_24213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24213 :=
  CNF.rup_sound cl_24213 [cl_602,cl_24209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_602 v h) (hints_cons _ _ _ (der_24209 v h) (by intro d hd; cases hd)))
def cl_24214 : CNF.NClause := [(71,true),(26,false),(7,false),(1,true),(20,true),(13,true)]
theorem der_24214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24214 :=
  CNF.rup_sound cl_24214 [cl_606,cl_24212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_606 v h) (hints_cons _ _ _ (der_24212 v h) (by intro d hd; cases hd)))
def cl_24215 : CNF.NClause := [(71,true),(20,false),(7,false),(13,false),(19,false),(26,true)]
theorem der_24215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24215 :=
  CNF.rup_sound cl_24215 [cl_610,cl_23600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_610 v h) (hints_cons _ _ _ (der_23600 v h) (by intro d hd; cases hd)))
def cl_24216 : CNF.NClause := [(71,true),(20,false),(7,false),(1,true),(19,false),(26,true)]
theorem der_24216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24216 :=
  CNF.rup_sound cl_24216 [cl_614,cl_24215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_614 v h) (hints_cons _ _ _ (der_24215 v h) (by intro d hd; cases hd)))
def cl_24217 : CNF.NClause := [(71,true),(7,false),(13,false),(19,true),(1,true),(20,false)]
theorem der_24217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24217 :=
  CNF.rup_sound cl_24217 [cl_618,cl_24209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_618 v h) (hints_cons _ _ _ (der_24209 v h) (by intro d hd; cases hd)))
def cl_24218 : CNF.NClause := [(71,true),(20,false),(7,false),(19,true),(1,true),(26,true)]
theorem der_24218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24218 :=
  CNF.rup_sound cl_24218 [cl_622,cl_24217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_622 v h) (hints_cons _ _ _ (der_24217 v h) (by intro d hd; cases hd)))
def cl_24219 : CNF.NClause := [(71,true),(7,false),(13,false),(1,true),(20,true),(19,false)]
theorem der_24219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24219 :=
  CNF.rup_sound cl_24219 [cl_626,cl_24211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_626 v h) (hints_cons _ _ _ (der_24211 v h) (by intro d hd; cases hd)))
def cl_24220 : CNF.NClause := [(71,true),(26,true),(7,false),(1,true),(20,true),(19,false)]
theorem der_24220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24220 :=
  CNF.rup_sound cl_24220 [cl_630,cl_24219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_630 v h) (hints_cons _ _ _ (der_24219 v h) (by intro d hd; cases hd)))
def cl_24221 : CNF.NClause := [(71,true),(26,true),(7,false),(1,true),(20,true),(13,false)]
theorem der_24221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24221 :=
  CNF.rup_sound cl_24221 [cl_634,cl_24219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_634 v h) (hints_cons _ _ _ (der_24219 v h) (by intro d hd; cases hd)))
def cl_24222 : CNF.NClause := [(86,true),(29,false),(14,false),(1,true),(18,false),(22,false)]
theorem der_24222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24222 :=
  CNF.rup_sound cl_24222 [cl_1538,cl_24189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1538 v h) (hints_cons _ _ _ (der_24189 v h) (by intro d hd; cases hd)))
def cl_24223 : CNF.NClause := [(86,true),(29,false),(14,true),(18,false),(5,false),(22,false)]
theorem der_24223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24223 :=
  CNF.rup_sound cl_24223 [cl_1542,cl_1541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1542 v h) (hints_cons _ _ _ (inp_1541 v h) (by intro d hd; cases hd)))
def cl_24224 : CNF.NClause := [(86,true),(14,false),(5,false),(1,true),(22,false),(29,false)]
theorem der_24224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24224 :=
  CNF.rup_sound cl_24224 [cl_1546,cl_24222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1546 v h) (hints_cons _ _ _ (der_24222 v h) (by intro d hd; cases hd)))
def cl_24225 : CNF.NClause := [(86,true),(22,false),(5,false),(14,true),(18,true),(29,false)]
theorem der_24225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24225 :=
  CNF.rup_sound cl_24225 [cl_1550,cl_23608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1550 v h) (hints_cons _ _ _ (der_23608 v h) (by intro d hd; cases hd)))
def cl_24226 : CNF.NClause := [(86,true),(14,false),(29,false),(1,true),(18,false),(5,false)]
theorem der_24226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24226 :=
  CNF.rup_sound cl_24226 [cl_1554,cl_24222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1554 v h) (hints_cons _ _ _ (der_24222 v h) (by intro d hd; cases hd)))
def cl_24227 : CNF.NClause := [(86,true),(22,true),(29,false),(18,false),(5,false),(14,true)]
theorem der_24227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24227 :=
  CNF.rup_sound cl_24227 [cl_1558,cl_23607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1558 v h) (hints_cons _ _ _ (der_23607 v h) (by intro d hd; cases hd)))
def cl_24228 : CNF.NClause := [(86,true),(22,true),(29,false),(1,true),(5,false),(14,false)]
theorem der_24228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24228 :=
  CNF.rup_sound cl_24228 [cl_1562,cl_24226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1562 v h) (hints_cons _ _ _ (der_24226 v h) (by intro d hd; cases hd)))
def cl_24229 : CNF.NClause := [(86,true),(22,true),(5,false),(18,true),(14,true),(29,false)]
theorem der_24229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24229 :=
  CNF.rup_sound cl_24229 [cl_1566,cl_23609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1566 v h) (hints_cons _ _ _ (der_23609 v h) (by intro d hd; cases hd)))
def cl_24230 : CNF.NClause := [(86,true),(22,false),(14,false),(18,false),(1,true),(5,false)]
theorem der_24230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24230 :=
  CNF.rup_sound cl_24230 [cl_1570,cl_24222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1570 v h) (hints_cons _ _ _ (der_24222 v h) (by intro d hd; cases hd)))
def cl_24231 : CNF.NClause := [(86,true),(29,true),(22,false),(18,false),(1,true),(5,false)]
theorem der_24231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24231 :=
  CNF.rup_sound cl_24231 [cl_1574,cl_24230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1574 v h) (hints_cons _ _ _ (der_24230 v h) (by intro d hd; cases hd)))
def cl_24232 : CNF.NClause := [(86,true),(14,false),(29,true),(1,true),(5,false),(22,false)]
theorem der_24232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24232 :=
  CNF.rup_sound cl_24232 [cl_1578,cl_24231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1578 v h) (hints_cons _ _ _ (der_24231 v h) (by intro d hd; cases hd)))
def cl_24233 : CNF.NClause := [(86,true),(22,false),(29,true),(5,false),(14,true),(18,true)]
theorem der_24233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24233 :=
  CNF.rup_sound cl_24233 [cl_1582,cl_1581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1582 v h) (hints_cons _ _ _ (inp_1581 v h) (by intro d hd; cases hd)))
def cl_24234 : CNF.NClause := [(86,true),(5,false),(14,false),(1,true),(29,true),(18,false)]
theorem der_24234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24234 :=
  CNF.rup_sound cl_24234 [cl_1586,cl_24232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1586 v h) (hints_cons _ _ _ (der_24232 v h) (by intro d hd; cases hd)))
def cl_24235 : CNF.NClause := [(86,true),(29,true),(1,true),(18,false),(5,false),(14,true)]
theorem der_24235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24235 :=
  CNF.rup_sound cl_24235 [cl_1590,cl_24231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1590 v h) (hints_cons _ _ _ (der_24231 v h) (by intro d hd; cases hd)))
def cl_24236 : CNF.NClause := [(86,true),(29,true),(1,true),(18,true),(14,false),(5,false)]
theorem der_24236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24236 :=
  CNF.rup_sound cl_24236 [cl_1594,cl_24232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1594 v h) (hints_cons _ _ _ (der_24232 v h) (by intro d hd; cases hd)))
def cl_24237 : CNF.NClause := [(81,true),(28,false),(12,false),(15,false),(23,false),(1,true)]
theorem der_24237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24237 :=
  CNF.rup_sound cl_24237 [cl_1220,cl_24190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1220 v h) (hints_cons _ _ _ (der_24190 v h) (by intro d hd; cases hd)))
def cl_24238 : CNF.NClause := [(81,true),(28,false),(9,true),(15,false),(23,false),(1,true)]
theorem der_24238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24238 :=
  CNF.rup_sound cl_24238 [cl_1224,cl_24237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1224 v h) (hints_cons _ _ _ (der_24237 v h) (by intro d hd; cases hd)))
def cl_24239 : CNF.NClause := [(81,true),(28,false),(9,true),(12,false),(15,true),(23,false)]
theorem der_24239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24239 :=
  CNF.rup_sound cl_24239 [cl_1228,cl_1227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1228 v h) (hints_cons _ _ _ (inp_1227 v h) (by intro d hd; cases hd)))
def cl_24240 : CNF.NClause := [(81,true),(28,false),(9,true),(15,true),(23,false),(1,true)]
theorem der_24240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24240 :=
  CNF.rup_sound cl_24240 [cl_1232,cl_24239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1232 v h) (hints_cons _ _ _ (der_24239 v h) (by intro d hd; cases hd)))
def cl_24241 : CNF.NClause := [(81,true),(28,false),(9,true),(12,false),(15,false),(1,true)]
theorem der_24241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24241 :=
  CNF.rup_sound cl_24241 [cl_1236,cl_24237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1236 v h) (hints_cons _ _ _ (der_24237 v h) (by intro d hd; cases hd)))
def cl_24242 : CNF.NClause := [(81,true),(28,false),(9,true),(15,false),(23,true),(1,true)]
theorem der_24242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24242 :=
  CNF.rup_sound cl_24242 [cl_1240,cl_24241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1240 v h) (hints_cons _ _ _ (der_24241 v h) (by intro d hd; cases hd)))
def cl_24243 : CNF.NClause := [(81,true),(28,false),(9,true),(12,false),(15,true),(23,true)]
theorem der_24243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24243 :=
  CNF.rup_sound cl_24243 [cl_1244,cl_23569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1244 v h) (hints_cons _ _ _ (der_23569 v h) (by intro d hd; cases hd)))
def cl_24244 : CNF.NClause := [(81,true),(12,false),(15,false),(1,true),(23,false),(28,true)]
theorem der_24244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24244 :=
  CNF.rup_sound cl_24244 [cl_1252,cl_1250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1252 v h) (hints_cons _ _ _ (inp_1250 v h) (by intro d hd; cases hd)))
def cl_24245 : CNF.NClause := [(81,true),(23,false),(9,true),(12,true),(15,false),(28,true)]
theorem der_24245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24245 :=
  CNF.rup_sound cl_24245 [cl_1256,cl_1255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1256 v h) (hints_cons _ _ _ (inp_1255 v h) (by intro d hd; cases hd)))
def cl_24246 : CNF.NClause := [(81,true),(15,true),(9,true),(12,false),(1,true),(23,false)]
theorem der_24246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24246 :=
  CNF.rup_sound cl_24246 [cl_1260,cl_24239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1260 v h) (hints_cons _ _ _ (der_24239 v h) (by intro d hd; cases hd)))
def cl_24247 : CNF.NClause := [(81,true),(15,false),(9,true),(12,false),(1,true),(23,true)]
theorem der_24247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24247 :=
  CNF.rup_sound cl_24247 [cl_1268,cl_24241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1268 v h) (hints_cons _ _ _ (der_24241 v h) (by intro d hd; cases hd)))
def cl_24248 : CNF.NClause := [(76,true),(8,true),(17,false),(1,true),(24,false),(27,true)]
theorem der_24248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24248 :=
  CNF.rup_sound cl_24248 [cl_936,cl_23594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_936 v h) (hints_cons _ _ _ (der_23594 v h) (by intro d hd; cases hd)))
def cl_24249 : CNF.NClause := [(86,true),(5,true),(1,true),(18,false),(29,false),(14,false)]
theorem der_24249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24249 :=
  CNF.rup_sound cl_24249 [cl_1556,cl_24189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1556 v h) (hints_cons _ _ _ (der_24189 v h) (by intro d hd; cases hd)))
def cl_24250 : CNF.NClause := [(71,true),(20,false),(7,true),(13,false),(19,true),(26,false)]
theorem der_24250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24250 :=
  CNF.rup_sound cl_24250 [cl_588,cl_23241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_588 v h) (hints_cons _ _ _ (der_23241 v h) (by intro d hd; cases hd)))
def cl_24251 : CNF.NClause := [(71,true),(20,false),(7,true),(1,true),(13,false),(26,true)]
theorem der_24251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24251 :=
  CNF.rup_sound cl_24251 [cl_620,cl_23623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_620 v h) (hints_cons _ _ _ (der_23623 v h) (by intro d hd; cases hd)))
def cl_24252 : CNF.NClause := [(81,true),(28,false),(1,true),(9,false),(23,false),(15,false)]
theorem der_24252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24252 :=
  CNF.rup_sound cl_24252 [cl_1222,cl_24190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1222 v h) (hints_cons _ _ _ (der_24190 v h) (by intro d hd; cases hd)))
def cl_24253 : CNF.NClause := [(81,true),(28,false),(15,false),(12,true),(1,true),(23,true)]
theorem der_24253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24253 :=
  CNF.rup_sound cl_24253 [cl_1238,cl_24242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1238 v h) (hints_cons _ _ _ (der_24242 v h) (by intro d hd; cases hd)))
def cl_24254 : CNF.NClause := [(81,true),(15,false),(1,true),(23,true),(9,false),(12,true)]
theorem der_24254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24254 :=
  CNF.rup_sound cl_24254 [cl_1270,cl_24253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1270 v h) (hints_cons _ _ _ (der_24253 v h) (by intro d hd; cases hd)))
def cl_24255 : CNF.NClause := [(81,true),(28,false),(9,false),(15,false),(12,false),(1,true)]
theorem der_24255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24255 :=
  CNF.rup_sound cl_24255 [cl_1234,cl_24190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1234 v h) (hints_cons _ _ _ (der_24190 v h) (by intro d hd; cases hd)))
def cl_24256 : CNF.NClause := [(81,true),(12,false),(28,true),(9,false),(15,false),(1,true)]
theorem der_24256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24256 :=
  CNF.rup_sound cl_24256 [cl_1266,cl_1250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1266 v h) (hints_cons _ _ _ (inp_1250 v h) (by intro d hd; cases hd)))
def cl_24257 : CNF.NClause := [(69,true),(20,false),(2,true),(9,false),(27,true),(11,false)]
theorem der_24257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24257 :=
  CNF.rup_sound cl_24257 [cl_482,cl_23581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_482 v h) (hints_cons _ _ _ (der_23581 v h) (by intro d hd; cases hd)))
def cl_24258 : CNF.NClause := [(69,true),(20,false),(27,true),(11,false),(18,false),(9,false)]
theorem der_24258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24258 :=
  CNF.rup_sound cl_24258 [cl_481,cl_24257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_481 v h) (hints_cons _ _ _ (der_24257 v h) (by intro d hd; cases hd)))
def cl_24259 : CNF.NClause := [(78,true),(15,false),(4,true),(27,true),(22,false),(13,false)]
theorem der_24259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24259 :=
  CNF.rup_sound cl_24259 [cl_1058,cl_24054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1058 v h) (hints_cons _ _ _ (der_24054 v h) (by intro d hd; cases hd)))
def cl_24260 : CNF.NClause := [(69,true),(9,true),(11,false),(2,true),(18,false),(27,true)]
theorem der_24260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24260 :=
  CNF.rup_sound cl_24260 [cl_484,cl_24186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_484 v h) (hints_cons _ _ _ (der_24186 v h) (by intro d hd; cases hd)))
def cl_24261 : CNF.NClause := [(83,true),(4,false),(5,true),(23,true),(17,false),(26,false)]
theorem der_24261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24261 :=
  CNF.rup_sound cl_24261 [cl_1367,cl_24122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1367 v h) (hints_cons _ _ _ (der_24122 v h) (by intro d hd; cases hd)))
def cl_24262 : CNF.NClause := [(83,true),(11,true),(4,false),(5,true),(17,false),(26,true)]
theorem der_24262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24262 :=
  CNF.rup_sound cl_24262 [cl_1399,cl_24105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1399 v h) (hints_cons _ _ _ (der_24105 v h) (by intro d hd; cases hd)))
def cl_24263 : CNF.NClause := [(83,true),(26,false),(4,false),(11,false),(17,false),(5,false)]
theorem der_24263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24263 :=
  CNF.rup_sound cl_24263 [cl_1361,cl_23611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1361 v h) (hints_cons _ _ _ (der_23611 v h) (by intro d hd; cases hd)))
def cl_24264 : CNF.NClause := [(83,true),(4,false),(11,false),(17,false),(26,true),(5,false)]
theorem der_24264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24264 :=
  CNF.rup_sound cl_24264 [cl_1393,cl_23611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1393 v h) (hints_cons _ _ _ (der_23611 v h) (by intro d hd; cases hd)))
def cl_24265 : CNF.NClause := [(74,true),(10,false),(29,false),(2,false),(6,false),(19,false)]
theorem der_24265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24265 :=
  CNF.rup_sound cl_24265 [cl_785,cl_769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_785 v h) (hints_cons _ _ _ (inp_769 v h) (by intro d hd; cases hd)))
def cl_24266 : CNF.NClause := [(74,true),(19,false),(6,false),(29,true),(10,false),(23,true)]
theorem der_24266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24266 :=
  CNF.rup_sound cl_24266 [cl_817,cl_24046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_817 v h) (hints_cons _ _ _ (der_24046 v h) (by intro d hd; cases hd)))
def cl_24267 : CNF.NClause := [(81,true),(12,false),(28,false),(1,false),(9,true),(23,true)]
theorem der_24267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24267 :=
  CNF.rup_sound cl_24267 [cl_1235,cl_23569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1235 v h) (hints_cons _ _ _ (der_23569 v h) (by intro d hd; cases hd)))
def cl_24268 : CNF.NClause := [(81,true),(12,false),(9,true),(15,false),(1,false),(28,true)]
theorem der_24268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24268 :=
  CNF.rup_sound cl_24268 [cl_1267,cl_23553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1267 v h) (hints_cons _ _ _ (der_23553 v h) (by intro d hd; cases hd)))
def cl_24269 : CNF.NClause := [(81,true),(28,false),(1,false),(15,false),(12,false),(9,false)]
theorem der_24269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24269 :=
  CNF.rup_sound cl_24269 [cl_1233,cl_23633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1233 v h) (hints_cons _ _ _ (der_23633 v h) (by intro d hd; cases hd)))
def cl_24270 : CNF.NClause := [(81,true),(15,false),(12,false),(9,false),(1,false),(28,true)]
theorem der_24270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24270 :=
  CNF.rup_sound cl_24270 [cl_1265,cl_23551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1265 v h) (hints_cons _ _ _ (der_23551 v h) (by intro d hd; cases hd)))
def cl_24271 : CNF.NClause := [(75,true),(10,false),(3,true),(9,false),(22,true),(26,false)]
theorem der_24271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24271 :=
  CNF.rup_sound cl_24271 [cl_850,cl_23555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_850 v h) (hints_cons _ _ _ (der_23555 v h) (by intro d hd; cases hd)))
def cl_24272 : CNF.NClause := [(68,true),(20,false),(16,false),(4,false),(8,false),(29,false)]
theorem der_24272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24272 :=
  CNF.rup_sound cl_24272 [cl_385,cl_389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_385 v h) (hints_cons _ _ _ (inp_389 v h) (by intro d hd; cases hd)))
def cl_24273 : CNF.NClause := [(75,true),(26,true),(3,false),(10,false),(9,false),(22,true)]
theorem der_24273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24273 :=
  CNF.rup_sound cl_24273 [cl_881,cl_23559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_881 v h) (hints_cons _ _ _ (der_23559 v h) (by intro d hd; cases hd)))
def cl_24274 : CNF.NClause := [(78,true),(27,true),(13,false),(15,false),(4,false),(6,false)]
theorem der_24274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24274 :=
  CNF.rup_sound cl_24274 [cl_1057,cl_1073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1057 v h) (hints_cons _ _ _ (inp_1073 v h) (by intro d hd; cases hd)))
def cl_24275 : CNF.NClause := [(75,true),(10,false),(3,true),(9,false),(26,true),(22,false)]
theorem der_24275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24275 :=
  CNF.rup_sound cl_24275 [cl_866,cl_23556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_866 v h) (hints_cons _ _ _ (der_23556 v h) (by intro d hd; cases hd)))
def cl_24276 : CNF.NClause := [(75,true),(26,true),(22,false),(3,false),(10,false),(9,false)]
theorem der_24276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24276 :=
  CNF.rup_sound cl_24276 [cl_865,cl_23558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_865 v h) (hints_cons _ _ _ (der_23558 v h) (by intro d hd; cases hd)))
def cl_24277 : CNF.NClause := [(81,true),(28,false),(1,false),(15,false),(23,false),(9,false)]
theorem der_24277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24277 :=
  CNF.rup_sound cl_24277 [cl_1221,cl_23633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1221 v h) (hints_cons _ _ _ (der_23633 v h) (by intro d hd; cases hd)))
def cl_24278 : CNF.NClause := [(81,true),(28,false),(1,false),(12,true),(9,false),(23,false)]
theorem der_24278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24278 :=
  CNF.rup_sound cl_24278 [cl_1229,cl_24277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1229 v h) (hints_cons _ _ _ (der_24277 v h) (by intro d hd; cases hd)))
def cl_24279 : CNF.NClause := [(81,true),(28,false),(12,true),(23,true),(15,false),(9,false)]
theorem der_24279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24279 :=
  CNF.rup_sound cl_24279 [cl_1237,cl_24253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1237 v h) (hints_cons _ _ _ (der_24253 v h) (by intro d hd; cases hd)))
def cl_24280 : CNF.NClause := [(81,true),(28,false),(1,false),(12,true),(15,true),(9,false)]
theorem der_24280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24280 :=
  CNF.rup_sound cl_24280 [cl_1245,cl_24278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1245 v h) (hints_cons _ _ _ (der_24278 v h) (by intro d hd; cases hd)))
def cl_24281 : CNF.NClause := [(81,true),(15,false),(23,false),(9,false),(28,true),(1,false)]
theorem der_24281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24281 :=
  CNF.rup_sound cl_24281 [cl_1253,cl_23551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1253 v h) (hints_cons _ _ _ (der_23551 v h) (by intro d hd; cases hd)))
def cl_24282 : CNF.NClause := [(81,true),(23,false),(9,false),(12,true),(1,false),(28,true)]
theorem der_24282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24282 :=
  CNF.rup_sound cl_24282 [cl_1261,cl_24281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1261 v h) (hints_cons _ _ _ (der_24281 v h) (by intro d hd; cases hd)))
def cl_24283 : CNF.NClause := [(81,true),(15,false),(12,true),(9,false),(1,false),(28,true)]
theorem der_24283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24283 :=
  CNF.rup_sound cl_24283 [cl_1269,cl_24281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1269 v h) (hints_cons _ _ _ (der_24281 v h) (by intro d hd; cases hd)))
def cl_24284 : CNF.NClause := [(81,true),(12,true),(23,true),(9,false),(1,false),(28,true)]
theorem der_24284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24284 :=
  CNF.rup_sound cl_24284 [cl_1277,cl_24283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1277 v h) (hints_cons _ _ _ (der_24283 v h) (by intro d hd; cases hd)))
def cl_24285 : CNF.NClause := [(85,true),(5,true),(19,false),(27,false),(12,true),(21,false)]
theorem der_24285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24285 :=
  CNF.rup_sound cl_24285 [cl_1480,cl_24091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1480 v h) (hints_cons _ _ _ (der_24091 v h) (by intro d hd; cases hd)))
def cl_24286 : CNF.NClause := [(85,true),(3,true),(5,true),(27,false),(12,true),(19,false)]
theorem der_24286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24286 :=
  CNF.rup_sound cl_24286 [cl_1496,cl_24285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1496 v h) (hints_cons _ _ _ (der_24285 v h) (by intro d hd; cases hd)))
def cl_24287 : CNF.NClause := [(85,true),(12,true),(3,true),(21,false),(5,true),(19,false)]
theorem der_24287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24287 :=
  CNF.rup_sound cl_24287 [cl_1512,cl_24285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1512 v h) (hints_cons _ _ _ (der_24285 v h) (by intro d hd; cases hd)))
def cl_24288 : CNF.NClause := [(85,true),(12,true),(27,false),(5,false),(19,true),(3,false)]
theorem der_24288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24288 :=
  CNF.rup_sound cl_24288 [cl_1485,cl_23644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1485 v h) (hints_cons _ _ _ (der_23644 v h) (by intro d hd; cases hd)))
def cl_24289 : CNF.NClause := [(85,true),(12,true),(5,false),(3,false),(19,true),(27,true)]
theorem der_24289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24289 :=
  CNF.rup_sound cl_24289 [cl_1517,cl_23645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1517 v h) (hints_cons _ _ _ (der_23645 v h) (by intro d hd; cases hd)))
def cl_24290 : CNF.NClause := [(84,true),(28,false),(5,true),(24,false),(16,true),(13,true)]
theorem der_24290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24290 :=
  CNF.rup_sound cl_24290 [cl_1424,cl_24079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1424 v h) (hints_cons _ _ _ (der_24079 v h) (by intro d hd; cases hd)))
def cl_24291 : CNF.NClause := [(69,true),(27,false),(2,true),(9,false),(11,false),(20,false)]
theorem der_24291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24291 :=
  CNF.rup_sound cl_24291 [cl_450,cl_23579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_450 v h) (hints_cons _ _ _ (der_23579 v h) (by intro d hd; cases hd)))
def cl_24292 : CNF.NClause := [(79,true),(15,true),(2,true),(26,false),(14,false),(21,false)]
theorem der_24292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24292 :=
  CNF.rup_sound cl_24292 [cl_1100,cl_23502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1100 v h) (hints_cons _ _ _ (der_23502 v h) (by intro d hd; cases hd)))
def cl_24293 : CNF.NClause := [(79,true),(2,true),(26,false),(14,false),(15,false),(21,false)]
theorem der_24293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24293 :=
  CNF.rup_sound cl_24293 [cl_1092,cl_1090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1092 v h) (hints_cons _ _ _ (inp_1090 v h) (by intro d hd; cases hd)))
def cl_24294 : CNF.NClause := [(79,true),(15,false),(2,true),(26,false),(14,true),(21,false)]
theorem der_24294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24294 :=
  CNF.rup_sound cl_24294 [cl_1096,cl_23501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1096 v h) (hints_cons _ _ _ (der_23501 v h) (by intro d hd; cases hd)))
def cl_24295 : CNF.NClause := [(68,true),(29,true),(4,false),(12,true),(20,false),(16,true)]
theorem der_24295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24295 :=
  CNF.rup_sound cl_24295 [cl_431,cl_23519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_431 v h) (hints_cons _ _ _ (der_23519 v h) (by intro d hd; cases hd)))
def cl_24296 : CNF.NClause := [(68,true),(4,false),(8,false),(29,true),(16,false),(20,false)]
theorem der_24296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24296 :=
  CNF.rup_sound cl_24296 [cl_417,cl_23518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_417 v h) (hints_cons _ _ _ (der_23518 v h) (by intro d hd; cases hd)))
def cl_24297 : CNF.NClause := [(86,true),(14,false),(18,false),(5,true),(1,true),(22,false)]
theorem der_24297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24297 :=
  CNF.rup_sound cl_24297 [cl_1572,cl_24189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1572 v h) (hints_cons _ _ _ (der_24189 v h) (by intro d hd; cases hd)))
def cl_24298 : CNF.NClause := [(86,true),(22,false),(5,false),(29,true),(18,false),(14,false)]
theorem der_24298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24298 :=
  CNF.rup_sound cl_24298 [cl_1569,cl_24232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1569 v h) (hints_cons _ _ _ (der_24232 v h) (by intro d hd; cases hd)))
def cl_24299 : CNF.NClause := [(74,true),(19,false),(6,false),(29,true),(10,false),(23,false)]
theorem der_24299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24299 :=
  CNF.rup_sound cl_24299 [cl_801,cl_802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_801 v h) (hints_cons _ _ _ (inp_802 v h) (by intro d hd; cases hd)))
def cl_24300 : CNF.NClause := [(80,true),(24,false),(7,false),(11,false),(15,false),(3,false)]
theorem der_24300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24300 :=
  CNF.rup_sound cl_24300 [cl_1185,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1185 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24301 : CNF.NClause := [(68,true),(20,false),(4,false),(12,true),(29,true),(16,false)]
theorem der_24301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24301 :=
  CNF.rup_sound cl_24301 [cl_423,cl_23518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_423 v h) (hints_cons _ _ _ (der_23518 v h) (by intro d hd; cases hd)))
def cl_24302 : CNF.NClause := [(80,true),(29,true),(7,true),(24,false),(11,false),(15,false)]
theorem der_24302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24302 :=
  CNF.rup_sound cl_24302 [cl_1188,cl_24154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1188 v h) (hints_cons _ _ _ (der_24154 v h) (by intro d hd; cases hd)))
def cl_24303 : CNF.NClause := [(86,true),(22,false),(1,false),(29,true),(14,true),(5,false)]
theorem der_24303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24303 :=
  CNF.rup_sound cl_24303 [cl_1573,cl_1581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1573 v h) (hints_cons _ _ _ (inp_1581 v h) (by intro d hd; cases hd)))
def cl_24304 : CNF.NClause := [(86,true),(1,false),(29,true),(14,true),(22,true),(5,false)]
theorem der_24304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24304 :=
  CNF.rup_sound cl_24304 [cl_1589,cl_23588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1589 v h) (hints_cons _ _ _ (der_23588 v h) (by intro d hd; cases hd)))
def cl_24305 : CNF.NClause := [(80,true),(3,false),(29,false),(7,false),(11,false),(15,false)]
theorem der_24305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24305 :=
  CNF.rup_sound cl_24305 [cl_1169,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1169 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24306 : CNF.NClause := [(80,true),(15,false),(29,true),(7,false),(11,false),(3,false)]
theorem der_24306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24306 :=
  CNF.rup_sound cl_24306 [cl_1201,cl_24300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1201 v h) (hints_cons _ _ _ (der_24300 v h) (by intro d hd; cases hd)))
def cl_24307 : CNF.NClause := [(84,true),(28,false),(13,false),(5,false),(16,false),(24,true)]
theorem der_24307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24307 :=
  CNF.rup_sound cl_24307 [cl_1425,cl_23615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1425 v h) (hints_cons _ _ _ (der_23615 v h) (by intro d hd; cases hd)))
def cl_24308 : CNF.NClause := [(84,true),(28,true),(24,true),(5,false),(13,false),(16,false)]
theorem der_24308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24308 :=
  CNF.rup_sound cl_24308 [cl_1457,cl_23619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1457 v h) (hints_cons _ _ _ (der_23619 v h) (by intro d hd; cases hd)))
def cl_24309 : CNF.NClause := [(76,true),(8,true),(17,false),(1,true),(10,true),(27,false)]
theorem der_24309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24309 :=
  CNF.rup_sound cl_24309 [cl_920,cl_24191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_920 v h) (hints_cons _ _ _ (der_24191 v h) (by intro d hd; cases hd)))
def cl_24310 : CNF.NClause := [(76,true),(27,false),(1,false),(8,false),(10,false),(17,false)]
theorem der_24310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24310 :=
  CNF.rup_sound cl_24310 [cl_913,cl_23610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_913 v h) (hints_cons _ _ _ (der_23610 v h) (by intro d hd; cases hd)))
def cl_24311 : CNF.NClause := [(76,true),(10,false),(1,false),(8,false),(27,true),(17,false)]
theorem der_24311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24311 :=
  CNF.rup_sound cl_24311 [cl_945,cl_929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_945 v h) (hints_cons _ _ _ (inp_929 v h) (by intro d hd; cases hd)))
def cl_24312 : CNF.NClause := [(80,true),(29,false),(7,true),(11,false),(15,false),(24,true)]
theorem der_24312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24312 :=
  CNF.rup_sound cl_24312 [cl_1172,cl_24150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1172 v h) (hints_cons _ _ _ (der_24150 v h) (by intro d hd; cases hd)))
def cl_24313 : CNF.NClause := [(80,true),(3,true),(15,false),(11,false),(7,true),(24,true)]
theorem der_24313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24313 :=
  CNF.rup_sound cl_24313 [cl_1204,cl_24312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1204 v h) (hints_cons _ _ _ (der_24312 v h) (by intro d hd; cases hd)))
def cl_24314 : CNF.NClause := [(76,true),(8,true),(27,false),(10,false),(17,false),(1,false)]
theorem der_24314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24314 :=
  CNF.rup_sound cl_24314 [cl_915,cl_23990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_915 v h) (hints_cons _ _ _ (der_23990 v h) (by intro d hd; cases hd)))
def cl_24315 : CNF.NClause := [(76,true),(27,false),(1,true),(8,true),(17,false),(10,false)]
theorem der_24315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24315 :=
  CNF.rup_sound cl_24315 [cl_916,cl_900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_916 v h) (hints_cons _ _ _ (inp_900 v h) (by intro d hd; cases hd)))
def cl_24316 : CNF.NClause := [(76,true),(10,false),(1,true),(8,true),(17,false),(27,true)]
theorem der_24316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24316 :=
  CNF.rup_sound cl_24316 [cl_948,cl_23594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_948 v h) (hints_cons _ _ _ (der_23594 v h) (by intro d hd; cases hd)))
def cl_24317 : CNF.NClause := [(80,true),(3,false),(7,false),(11,false),(24,false),(29,false)]
theorem der_24317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24317 :=
  CNF.rup_sound cl_24317 [cl_1161,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1161 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24318 : CNF.NClause := [(80,true),(15,true),(3,false),(11,false),(24,true),(29,false)]
theorem der_24318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24318 :=
  CNF.rup_sound cl_24318 [cl_1177,cl_24152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1177 v h) (hints_cons _ _ _ (der_24152 v h) (by intro d hd; cases hd)))
def cl_24319 : CNF.NClause := [(80,true),(15,true),(3,false),(11,false),(24,false),(29,true)]
theorem der_24319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24319 :=
  CNF.rup_sound cl_24319 [cl_1193,cl_24156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1193 v h) (hints_cons _ _ _ (der_24156 v h) (by intro d hd; cases hd)))
def cl_24320 : CNF.NClause := [(80,true),(15,true),(3,false),(11,false),(24,true),(29,true)]
theorem der_24320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24320 :=
  CNF.rup_sound cl_24320 [cl_1209,cl_24160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1209 v h) (hints_cons _ _ _ (der_24160 v h) (by intro d hd; cases hd)))
def cl_24321 : CNF.NClause := [(81,true),(28,false),(1,true),(9,false),(12,false),(23,false)]
theorem der_24321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24321 :=
  CNF.rup_sound cl_24321 [cl_1226,cl_24190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1226 v h) (hints_cons _ _ _ (der_24190 v h) (by intro d hd; cases hd)))
def cl_24322 : CNF.NClause := [(81,true),(28,false),(15,true),(9,false),(12,false),(1,true)]
theorem der_24322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24322 :=
  CNF.rup_sound cl_24322 [cl_1242,cl_24321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1242 v h) (hints_cons _ _ _ (der_24321 v h) (by intro d hd; cases hd)))
def cl_24323 : CNF.NClause := [(81,true),(12,false),(28,true),(9,false),(23,false),(1,true)]
theorem der_24323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24323 :=
  CNF.rup_sound cl_24323 [cl_1258,cl_1250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1258 v h) (hints_cons _ _ _ (inp_1250 v h) (by intro d hd; cases hd)))
def cl_24324 : CNF.NClause := [(81,true),(12,false),(28,true),(1,true),(23,true),(9,false)]
theorem der_24324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24324 :=
  CNF.rup_sound cl_24324 [cl_1274,cl_24256] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1274 v h) (hints_cons _ _ _ (der_24256 v h) (by intro d hd; cases hd)))
def cl_24325 : CNF.NClause := [(81,true),(28,false),(1,false),(23,false),(12,false),(15,true)]
theorem der_24325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24325 :=
  CNF.rup_sound cl_24325 [cl_1225,cl_1227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1225 v h) (hints_cons _ _ _ (inp_1227 v h) (by intro d hd; cases hd)))
def cl_24326 : CNF.NClause := [(81,true),(12,false),(1,false),(15,true),(23,true),(28,false)]
theorem der_24326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24326 :=
  CNF.rup_sound cl_24326 [cl_1241,cl_23569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1241 v h) (hints_cons _ _ _ (der_23569 v h) (by intro d hd; cases hd)))
def cl_24327 : CNF.NClause := [(81,true),(23,false),(12,false),(9,false),(28,true),(1,false)]
theorem der_24327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24327 :=
  CNF.rup_sound cl_24327 [cl_1257,cl_23551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1257 v h) (hints_cons _ _ _ (der_23551 v h) (by intro d hd; cases hd)))
def cl_24328 : CNF.NClause := [(81,true),(15,true),(12,false),(9,false),(1,false),(28,true)]
theorem der_24328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24328 :=
  CNF.rup_sound cl_24328 [cl_1273,cl_24327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1273 v h) (hints_cons _ _ _ (der_24327 v h) (by intro d hd; cases hd)))
def cl_24329 : CNF.NClause := [(78,true),(4,false),(6,false),(22,false),(13,false),(27,false)]
theorem der_24329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24329 :=
  CNF.rup_sound cl_24329 [cl_1033,cl_1025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1033 v h) (hints_cons _ _ _ (inp_1025 v h) (by intro d hd; cases hd)))
def cl_24330 : CNF.NClause := [(78,true),(4,false),(13,false),(6,false),(22,true),(27,false)]
theorem der_24330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24330 :=
  CNF.rup_sound cl_24330 [cl_1049,cl_23632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1049 v h) (hints_cons _ _ _ (der_23632 v h) (by intro d hd; cases hd)))
def cl_24331 : CNF.NClause := [(78,true),(15,true),(4,false),(6,false),(22,false),(13,false)]
theorem der_24331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24331 :=
  CNF.rup_sound cl_24331 [cl_1065,cl_24329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1065 v h) (hints_cons _ _ _ (der_24329 v h) (by intro d hd; cases hd)))
def cl_24332 : CNF.NClause := [(78,true),(4,false),(6,false),(27,true),(22,true),(13,false)]
theorem der_24332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24332 :=
  CNF.rup_sound cl_24332 [cl_1081,cl_1073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1081 v h) (hints_cons _ _ _ (inp_1073 v h) (by intro d hd; cases hd)))
def cl_24333 : CNF.NClause := [(79,true),(14,false),(26,false),(8,false),(15,true),(21,false)]
theorem der_24333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24333 :=
  CNF.rup_sound cl_24333 [cl_1097,cl_23502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1097 v h) (hints_cons _ _ _ (der_23502 v h) (by intro d hd; cases hd)))
def cl_24334 : CNF.NClause := [(79,true),(2,false),(26,false),(8,false),(15,true),(21,true)]
theorem der_24334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24334 :=
  CNF.rup_sound cl_24334 [cl_1113,cl_23604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1113 v h) (hints_cons _ _ _ (der_23604 v h) (by intro d hd; cases hd)))
def cl_24335 : CNF.NClause := [(79,true),(14,false),(26,true),(8,false),(15,true),(21,false)]
theorem der_24335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24335 :=
  CNF.rup_sound cl_24335 [cl_1129,cl_23510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1129 v h) (hints_cons _ _ _ (der_23510 v h) (by intro d hd; cases hd)))
def cl_24336 : CNF.NClause := [(79,true),(26,true),(15,true),(8,false),(2,false),(14,false)]
theorem der_24336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24336 :=
  CNF.rup_sound cl_24336 [cl_1145,cl_24335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1145 v h) (hints_cons _ _ _ (der_24335 v h) (by intro d hd; cases hd)))
def cl_24337 : CNF.NClause := [(80,true),(29,false),(7,true),(11,true),(15,true),(24,false)]
theorem der_24337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24337 :=
  CNF.rup_sound cl_24337 [cl_1168,cl_24149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1168 v h) (hints_cons _ _ _ (der_24149 v h) (by intro d hd; cases hd)))
def cl_24338 : CNF.NClause := [(81,true),(28,false),(1,true),(9,false),(15,true),(23,false)]
theorem der_24338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24338 :=
  CNF.rup_sound cl_24338 [cl_1230,cl_24321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1230 v h) (hints_cons _ _ _ (der_24321 v h) (by intro d hd; cases hd)))
def cl_24339 : CNF.NClause := [(81,true),(28,true),(23,false),(9,false),(15,true),(12,true)]
theorem der_24339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24339 :=
  CNF.rup_sound cl_24339 [cl_1262,cl_24282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1262 v h) (hints_cons _ _ _ (der_24282 v h) (by intro d hd; cases hd)))
def cl_24340 : CNF.NClause := [(78,true),(6,true),(4,false),(15,true),(22,false),(27,false)]
theorem der_24340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24340 :=
  CNF.rup_sound cl_24340 [cl_1039,cl_24033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1039 v h) (hints_cons _ _ _ (der_24033 v h) (by intro d hd; cases hd)))
def cl_24341 : CNF.NClause := [(78,true),(15,true),(4,false),(27,true),(22,false),(6,true)]
theorem der_24341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24341 :=
  CNF.rup_sound cl_24341 [cl_1071,cl_24037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1071 v h) (hints_cons _ _ _ (der_24037 v h) (by intro d hd; cases hd)))
def cl_24342 : CNF.NClause := [(78,true),(15,true),(4,false),(22,true),(6,true),(27,false)]
theorem der_24342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24342 :=
  CNF.rup_sound cl_24342 [cl_1055,cl_24035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1055 v h) (hints_cons _ _ _ (der_24035 v h) (by intro d hd; cases hd)))
def cl_24343 : CNF.NClause := [(81,true),(28,false),(9,false),(12,true),(1,true),(23,true)]
theorem der_24343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24343 :=
  CNF.rup_sound cl_24343 [cl_1246,cl_24253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1246 v h) (hints_cons _ _ _ (der_24253 v h) (by intro d hd; cases hd)))
def cl_24344 : CNF.NClause := [(79,true),(15,true),(2,true),(26,false),(21,false),(14,true)]
theorem der_24344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24344 :=
  CNF.rup_sound cl_24344 [cl_1104,cl_23503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1104 v h) (hints_cons _ _ _ (der_23503 v h) (by intro d hd; cases hd)))
def cl_24345 : CNF.NClause := [(80,true),(15,true),(7,true),(11,false),(24,false),(29,false)]
theorem der_24345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24345 :=
  CNF.rup_sound cl_24345 [cl_1164,cl_24148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1164 v h) (hints_cons _ _ _ (der_24148 v h) (by intro d hd; cases hd)))
def cl_24346 : CNF.NClause := [(80,true),(29,false),(7,true),(11,false),(24,true),(15,true)]
theorem der_24346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24346 :=
  CNF.rup_sound cl_24346 [cl_1180,cl_24152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1180 v h) (hints_cons _ _ _ (der_24152 v h) (by intro d hd; cases hd)))
def cl_24347 : CNF.NClause := [(80,true),(15,true),(7,true),(11,false),(24,false),(29,true)]
theorem der_24347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24347 :=
  CNF.rup_sound cl_24347 [cl_1196,cl_24156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1196 v h) (hints_cons _ _ _ (der_24156 v h) (by intro d hd; cases hd)))
def cl_24348 : CNF.NClause := [(79,true),(15,true),(21,false),(2,true),(14,false),(26,true)]
theorem der_24348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24348 :=
  CNF.rup_sound cl_24348 [cl_1132,cl_23510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1132 v h) (hints_cons _ _ _ (der_23510 v h) (by intro d hd; cases hd)))
def cl_24349 : CNF.NClause := [(78,true),(15,true),(4,true),(13,false),(22,false),(27,false)]
theorem der_24349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24349 :=
  CNF.rup_sound cl_24349 [cl_1034,cl_24049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1034 v h) (hints_cons _ _ _ (der_24049 v h) (by intro d hd; cases hd)))
def cl_24350 : CNF.NClause := [(78,true),(15,true),(4,true),(13,false),(6,false),(27,false)]
theorem der_24350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24350 :=
  CNF.rup_sound cl_24350 [cl_1050,cl_24349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1050 v h) (hints_cons _ _ _ (der_24349 v h) (by intro d hd; cases hd)))
def cl_24351 : CNF.NClause := [(78,true),(4,true),(22,false),(13,false),(6,false),(27,true)]
theorem der_24351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24351 :=
  CNF.rup_sound cl_24351 [cl_1066,cl_24259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1066 v h) (hints_cons _ _ _ (der_24259 v h) (by intro d hd; cases hd)))
def cl_24352 : CNF.NClause := [(81,true),(28,false),(15,true),(23,false),(1,false),(9,true)]
theorem der_24352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24352 :=
  CNF.rup_sound cl_24352 [cl_1231,cl_1227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1231 v h) (hints_cons _ _ _ (inp_1227 v h) (by intro d hd; cases hd)))
def cl_24353 : CNF.NClause := [(81,true),(28,false),(9,true),(15,true),(1,false),(23,true)]
theorem der_24353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24353 :=
  CNF.rup_sound cl_24353 [cl_1247,cl_23569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1247 v h) (hints_cons _ _ _ (der_23569 v h) (by intro d hd; cases hd)))
def cl_24354 : CNF.NClause := [(81,true),(12,true),(9,true),(1,false),(23,false),(28,true)]
theorem der_24354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24354 :=
  CNF.rup_sound cl_24354 [cl_1263,cl_1255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1263 v h) (hints_cons _ _ _ (inp_1255 v h) (by intro d hd; cases hd)))
def cl_24355 : CNF.NClause := [(83,true),(11,true),(5,false),(26,false),(17,false),(23,false)]
theorem der_24355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24355 :=
  CNF.rup_sound cl_24355 [cl_1349,cl_1350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1349 v h) (hints_cons _ _ _ (inp_1350 v h) (by intro d hd; cases hd)))
def cl_24356 : CNF.NClause := [(83,true),(11,true),(5,false),(26,false),(23,false),(17,true)]
theorem der_24356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24356 :=
  CNF.rup_sound cl_24356 [cl_1357,cl_23530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1357 v h) (hints_cons _ _ _ (der_23530 v h) (by intro d hd; cases hd)))
def cl_24357 : CNF.NClause := [(83,true),(11,true),(5,false),(17,false),(26,false),(23,true)]
theorem der_24357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24357 :=
  CNF.rup_sound cl_24357 [cl_1365,cl_23531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1365 v h) (hints_cons _ _ _ (der_23531 v h) (by intro d hd; cases hd)))
def cl_24358 : CNF.NClause := [(83,true),(11,true),(5,false),(23,true),(17,true),(26,false)]
theorem der_24358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24358 :=
  CNF.rup_sound cl_24358 [cl_1373,cl_23532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1373 v h) (hints_cons _ _ _ (der_23532 v h) (by intro d hd; cases hd)))
def cl_24359 : CNF.NClause := [(83,true),(23,false),(4,false),(5,false),(26,true),(17,false)]
theorem der_24359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24359 :=
  CNF.rup_sound cl_24359 [cl_1381,cl_23611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1381 v h) (hints_cons _ _ _ (der_23611 v h) (by intro d hd; cases hd)))
def cl_24360 : CNF.NClause := [(83,true),(11,true),(26,true),(5,false),(17,true),(23,false)]
theorem der_24360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24360 :=
  CNF.rup_sound cl_24360 [cl_1389,cl_23534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1389 v h) (hints_cons _ _ _ (der_23534 v h) (by intro d hd; cases hd)))
def cl_24361 : CNF.NClause := [(83,true),(11,true),(4,false),(17,false),(26,true),(23,true)]
theorem der_24361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24361 :=
  CNF.rup_sound cl_24361 [cl_1397,cl_24262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1397 v h) (hints_cons _ _ _ (der_24262 v h) (by intro d hd; cases hd)))
def cl_24362 : CNF.NClause := [(83,true),(11,true),(4,false),(5,false),(23,true),(26,true)]
theorem der_24362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24362 :=
  CNF.rup_sound cl_24362 [cl_1405,cl_24361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1405 v h) (hints_cons _ _ _ (der_24361 v h) (by intro d hd; cases hd)))
def cl_24363 : CNF.NClause := [(80,true),(3,false),(7,false),(15,false),(24,false),(29,false)]
theorem der_24363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24363 :=
  CNF.rup_sound cl_24363 [cl_1157,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1157 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24364 : CNF.NClause := [(80,true),(11,true),(3,false),(15,true),(24,false),(29,false)]
theorem der_24364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24364 :=
  CNF.rup_sound cl_24364 [cl_1165,cl_24149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1165 v h) (hints_cons _ _ _ (der_24149 v h) (by intro d hd; cases hd)))
def cl_24365 : CNF.NClause := [(80,true),(11,true),(3,false),(15,false),(24,true),(29,false)]
theorem der_24365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24365 :=
  CNF.rup_sound cl_24365 [cl_1173,cl_24151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1173 v h) (hints_cons _ _ _ (der_24151 v h) (by intro d hd; cases hd)))
def cl_24366 : CNF.NClause := [(80,true),(11,true),(3,false),(15,true),(24,true),(29,false)]
theorem der_24366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24366 :=
  CNF.rup_sound cl_24366 [cl_1181,cl_24153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1181 v h) (hints_cons _ _ _ (der_24153 v h) (by intro d hd; cases hd)))
def cl_24367 : CNF.NClause := [(80,true),(3,false),(7,false),(15,false),(24,false),(29,true)]
theorem der_24367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24367 :=
  CNF.rup_sound cl_24367 [cl_1189,cl_24300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1189 v h) (hints_cons _ _ _ (der_24300 v h) (by intro d hd; cases hd)))
def cl_24368 : CNF.NClause := [(80,true),(11,true),(3,false),(7,false),(15,true),(24,false)]
theorem der_24368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24368 :=
  CNF.rup_sound cl_24368 [cl_1197,cl_24364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1197 v h) (hints_cons _ _ _ (der_24364 v h) (by intro d hd; cases hd)))
def cl_24369 : CNF.NClause := [(80,true),(3,false),(7,false),(15,false),(24,true),(29,true)]
theorem der_24369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24369 :=
  CNF.rup_sound cl_24369 [cl_1205,cl_24306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1205 v h) (hints_cons _ _ _ (der_24306 v h) (by intro d hd; cases hd)))
def cl_24370 : CNF.NClause := [(80,true),(11,true),(3,false),(7,false),(15,true),(29,true)]
theorem der_24370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24370 :=
  CNF.rup_sound cl_24370 [cl_1213,cl_24368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1213 v h) (hints_cons _ _ _ (der_24368 v h) (by intro d hd; cases hd)))
def cl_24371 : CNF.NClause := [(69,true),(27,false),(2,false),(18,false),(9,false),(20,false)]
theorem der_24371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24371 :=
  CNF.rup_sound cl_24371 [cl_453,cl_449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_453 v h) (hints_cons _ _ _ (inp_449 v h) (by intro d hd; cases hd)))
def cl_24372 : CNF.NClause := [(69,true),(11,true),(27,false),(9,false),(20,false),(18,true)]
theorem der_24372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24372 :=
  CNF.rup_sound cl_24372 [cl_461,cl_462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_461 v h) (hints_cons _ _ _ (inp_462 v h) (by intro d hd; cases hd)))
def cl_24373 : CNF.NClause := [(69,true),(2,false),(27,false),(9,false),(18,false),(20,true)]
theorem der_24373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24373 :=
  CNF.rup_sound cl_24373 [cl_469,cl_24175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_469 v h) (hints_cons _ _ _ (der_24175 v h) (by intro d hd; cases hd)))
def cl_24374 : CNF.NClause := [(69,true),(11,true),(27,false),(9,false),(18,true),(20,true)]
theorem der_24374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24374 :=
  CNF.rup_sound cl_24374 [cl_477,cl_23575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_477 v h) (hints_cons _ _ _ (der_23575 v h) (by intro d hd; cases hd)))
def cl_24375 : CNF.NClause := [(69,true),(20,false),(27,true),(2,false),(9,false),(18,false)]
theorem der_24375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24375 :=
  CNF.rup_sound cl_24375 [cl_485,cl_24258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_485 v h) (hints_cons _ _ _ (der_24258 v h) (by intro d hd; cases hd)))
def cl_24376 : CNF.NClause := [(69,true),(20,false),(27,true),(11,true),(9,false),(18,true)]
theorem der_24376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24376 :=
  CNF.rup_sound cl_24376 [cl_493,cl_23576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_493 v h) (hints_cons _ _ _ (der_23576 v h) (by intro d hd; cases hd)))
def cl_24377 : CNF.NClause := [(69,true),(11,true),(27,true),(2,false),(9,false),(18,false)]
theorem der_24377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24377 :=
  CNF.rup_sound cl_24377 [cl_501,cl_24375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_501 v h) (hints_cons _ _ _ (der_24375 v h) (by intro d hd; cases hd)))
def cl_24378 : CNF.NClause := [(69,true),(11,true),(27,true),(2,false),(9,false),(18,true)]
theorem der_24378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24378 :=
  CNF.rup_sound cl_24378 [cl_509,cl_24376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_509 v h) (hints_cons _ _ _ (der_24376 v h) (by intro d hd; cases hd)))
def cl_24379 : CNF.NClause := [(69,true),(27,false),(2,true),(9,false),(11,true),(20,false)]
theorem der_24379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24379 :=
  CNF.rup_sound cl_24379 [cl_454,cl_462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_454 v h) (hints_cons _ _ _ (inp_462 v h) (by intro d hd; cases hd)))
def cl_24380 : CNF.NClause := [(69,true),(11,true),(2,true),(27,false),(9,false),(20,true)]
theorem der_24380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24380 :=
  CNF.rup_sound cl_24380 [cl_470,cl_23575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_470 v h) (hints_cons _ _ _ (der_23575 v h) (by intro d hd; cases hd)))
def cl_24381 : CNF.NClause := [(69,true),(20,false),(2,true),(9,false),(11,true),(27,true)]
theorem der_24381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24381 :=
  CNF.rup_sound cl_24381 [cl_486,cl_23576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_486 v h) (hints_cons _ _ _ (der_23576 v h) (by intro d hd; cases hd)))
def cl_24382 : CNF.NClause := [(69,true),(9,false),(2,true),(27,true),(18,false),(20,true)]
theorem der_24382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24382 :=
  CNF.rup_sound cl_24382 [cl_502,cl_24186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_502 v h) (hints_cons _ _ _ (der_24186 v h) (by intro d hd; cases hd)))
def cl_24383 : CNF.NClause := [(80,true),(29,false),(7,true),(11,true),(15,false),(24,false)]
theorem der_24383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24383 :=
  CNF.rup_sound cl_24383 [cl_1160,cl_24147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1160 v h) (hints_cons _ _ _ (der_24147 v h) (by intro d hd; cases hd)))
def cl_24384 : CNF.NClause := [(80,true),(29,false),(7,true),(15,false),(11,true),(24,true)]
theorem der_24384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24384 :=
  CNF.rup_sound cl_24384 [cl_1176,cl_24151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1176 v h) (hints_cons _ _ _ (der_24151 v h) (by intro d hd; cases hd)))
def cl_24385 : CNF.NClause := [(80,true),(24,false),(3,true),(7,true),(29,true),(15,false)]
theorem der_24385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24385 :=
  CNF.rup_sound cl_24385 [cl_1192,cl_24302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1192 v h) (hints_cons _ _ _ (der_24302 v h) (by intro d hd; cases hd)))
def cl_24386 : CNF.NClause := [(69,true),(27,false),(2,true),(11,true),(20,false),(18,false)]
theorem der_24386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24386 :=
  CNF.rup_sound cl_24386 [cl_456,cl_24379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_456 v h) (hints_cons _ _ _ (der_24379 v h) (by intro d hd; cases hd)))
def cl_24387 : CNF.NClause := [(69,true),(11,true),(2,true),(27,false),(20,false),(18,true)]
theorem der_24387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24387 :=
  CNF.rup_sound cl_24387 [cl_464,cl_462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_464 v h) (hints_cons _ _ _ (inp_462 v h) (by intro d hd; cases hd)))
def cl_24388 : CNF.NClause := [(69,true),(11,true),(18,false),(2,true),(27,false),(9,true)]
theorem der_24388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24388 :=
  CNF.rup_sound cl_24388 [cl_472,cl_24386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_472 v h) (hints_cons _ _ _ (der_24386 v h) (by intro d hd; cases hd)))
def cl_24389 : CNF.NClause := [(69,true),(9,true),(27,true),(2,true),(20,false),(18,false)]
theorem der_24389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24389 :=
  CNF.rup_sound cl_24389 [cl_488,cl_24260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_488 v h) (hints_cons _ _ _ (der_24260 v h) (by intro d hd; cases hd)))
def cl_24390 : CNF.NClause := [(70,true),(20,false),(17,false),(6,true),(14,false),(28,false)]
theorem der_24390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24390 :=
  CNF.rup_sound cl_24390 [cl_516,cl_24017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_516 v h) (hints_cons _ _ _ (der_24017 v h) (by intro d hd; cases hd)))
def cl_24391 : CNF.NClause := [(75,true),(26,false),(3,true),(9,false),(10,false),(22,false)]
theorem der_24391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24391 :=
  CNF.rup_sound cl_24391 [cl_834,cl_842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_834 v h) (hints_cons _ _ _ (inp_842 v h) (by intro d hd; cases hd)))
def cl_24392 : CNF.NClause := [(80,true),(29,false),(7,false),(11,false),(15,false),(24,false)]
theorem der_24392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24392 :=
  CNF.rup_sound cl_24392 [cl_1154,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1154 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24393 : CNF.NClause := [(80,true),(7,false),(3,true),(15,false),(24,false),(29,false)]
theorem der_24393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24393 :=
  CNF.rup_sound cl_24393 [cl_1158,cl_24392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1158 v h) (hints_cons _ _ _ (der_24392 v h) (by intro d hd; cases hd)))
def cl_24394 : CNF.NClause := [(80,true),(15,true),(11,false),(3,true),(24,false),(29,false)]
theorem der_24394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24394 :=
  CNF.rup_sound cl_24394 [cl_1162,cl_24345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1162 v h) (hints_cons _ _ _ (der_24345 v h) (by intro d hd; cases hd)))
def cl_24395 : CNF.NClause := [(80,true),(11,true),(7,false),(15,true),(24,false),(29,false)]
theorem der_24395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24395 :=
  CNF.rup_sound cl_24395 [cl_1166,cl_24364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1166 v h) (hints_cons _ _ _ (der_24364 v h) (by intro d hd; cases hd)))
def cl_24396 : CNF.NClause := [(80,true),(3,true),(11,false),(15,false),(24,true),(29,false)]
theorem der_24396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24396 :=
  CNF.rup_sound cl_24396 [cl_1170,cl_24312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1170 v h) (hints_cons _ _ _ (der_24312 v h) (by intro d hd; cases hd)))
def cl_24397 : CNF.NClause := [(80,true),(11,true),(3,true),(15,false),(24,true),(29,false)]
theorem der_24397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24397 :=
  CNF.rup_sound cl_24397 [cl_1174,cl_24384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1174 v h) (hints_cons _ _ _ (der_24384 v h) (by intro d hd; cases hd)))
def cl_24398 : CNF.NClause := [(80,true),(15,true),(7,false),(11,false),(3,true),(29,false)]
theorem der_24398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24398 :=
  CNF.rup_sound cl_24398 [cl_1178,cl_24394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1178 v h) (hints_cons _ _ _ (der_24394 v h) (by intro d hd; cases hd)))
def cl_24399 : CNF.NClause := [(80,true),(11,true),(7,false),(3,true),(15,true),(29,false)]
theorem der_24399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24399 :=
  CNF.rup_sound cl_24399 [cl_1182,cl_24395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1182 v h) (hints_cons _ _ _ (der_24395 v h) (by intro d hd; cases hd)))
def cl_24400 : CNF.NClause := [(80,true),(29,true),(7,false),(11,false),(15,false),(24,false)]
theorem der_24400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24400 :=
  CNF.rup_sound cl_24400 [cl_1186,cl_24300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1186 v h) (hints_cons _ _ _ (der_24300 v h) (by intro d hd; cases hd)))
def cl_24401 : CNF.NClause := [(80,true),(11,true),(7,false),(3,true),(15,false),(24,false)]
theorem der_24401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24401 :=
  CNF.rup_sound cl_24401 [cl_1190,cl_24393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1190 v h) (hints_cons _ _ _ (der_24393 v h) (by intro d hd; cases hd)))
def cl_24402 : CNF.NClause := [(80,true),(15,true),(7,false),(11,false),(3,true),(24,false)]
theorem der_24402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24402 :=
  CNF.rup_sound cl_24402 [cl_1194,cl_24394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1194 v h) (hints_cons _ _ _ (der_24394 v h) (by intro d hd; cases hd)))
def cl_24403 : CNF.NClause := [(80,true),(7,false),(3,true),(15,true),(24,false),(29,true)]
theorem der_24403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24403 :=
  CNF.rup_sound cl_24403 [cl_1198,cl_24402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1198 v h) (hints_cons _ _ _ (der_24402 v h) (by intro d hd; cases hd)))
def cl_24404 : CNF.NClause := [(80,true),(15,false),(7,false),(11,false),(24,true),(29,true)]
theorem der_24404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24404 :=
  CNF.rup_sound cl_24404 [cl_1202,cl_24369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1202 v h) (hints_cons _ _ _ (der_24369 v h) (by intro d hd; cases hd)))
def cl_24405 : CNF.NClause := [(80,true),(11,true),(7,false),(15,false),(24,true),(29,true)]
theorem der_24405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24405 :=
  CNF.rup_sound cl_24405 [cl_1206,cl_24369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1206 v h) (hints_cons _ _ _ (der_24369 v h) (by intro d hd; cases hd)))
def cl_24406 : CNF.NClause := [(80,true),(15,true),(3,true),(11,false),(7,false),(29,true)]
theorem der_24406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24406 :=
  CNF.rup_sound cl_24406 [cl_1210,cl_24403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1210 v h) (hints_cons _ _ _ (der_24403 v h) (by intro d hd; cases hd)))
def cl_24407 : CNF.NClause := [(70,true),(20,false),(6,false),(14,false),(17,false),(28,false)]
theorem der_24407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24407 :=
  CNF.rup_sound cl_24407 [cl_514,cl_513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_514 v h) (hints_cons _ _ _ (inp_513 v h) (by intro d hd; cases hd)))
def cl_24408 : CNF.NClause := [(70,true),(20,false),(6,false),(14,true),(17,false),(28,false)]
theorem der_24408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24408 :=
  CNF.rup_sound cl_24408 [cl_518,cl_23612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_518 v h) (hints_cons _ _ _ (der_23612 v h) (by intro d hd; cases hd)))
def cl_24409 : CNF.NClause := [(70,true),(28,false),(6,false),(3,true),(14,false),(20,false)]
theorem der_24409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24409 :=
  CNF.rup_sound cl_24409 [cl_522,cl_24407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_522 v h) (hints_cons _ _ _ (der_24407 v h) (by intro d hd; cases hd)))
def cl_24410 : CNF.NClause := [(70,true),(20,false),(3,true),(14,true),(17,true),(28,false)]
theorem der_24410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24410 :=
  CNF.rup_sound cl_24410 [cl_526,cl_24059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_526 v h) (hints_cons _ _ _ (der_24059 v h) (by intro d hd; cases hd)))
def cl_24411 : CNF.NClause := [(70,true),(28,false),(17,false),(3,true),(14,false),(20,true)]
theorem der_24411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24411 :=
  CNF.rup_sound cl_24411 [cl_530,cl_24169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_530 v h) (hints_cons _ _ _ (der_24169 v h) (by intro d hd; cases hd)))
def cl_24412 : CNF.NClause := [(70,true),(28,false),(3,true),(6,false),(20,true),(17,false)]
theorem der_24412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24412 :=
  CNF.rup_sound cl_24412 [cl_534,cl_24411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_534 v h) (hints_cons _ _ _ (der_24411 v h) (by intro d hd; cases hd)))
def cl_24413 : CNF.NClause := [(70,true),(28,false),(3,true),(14,false),(20,true),(6,false)]
theorem der_24413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24413 :=
  CNF.rup_sound cl_24413 [cl_538,cl_24411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_538 v h) (hints_cons _ _ _ (der_24411 v h) (by intro d hd; cases hd)))
def cl_24414 : CNF.NClause := [(70,true),(20,true),(6,false),(3,true),(14,true),(28,false)]
theorem der_24414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24414 :=
  CNF.rup_sound cl_24414 [cl_542,cl_24412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_542 v h) (hints_cons _ _ _ (der_24412 v h) (by intro d hd; cases hd)))
def cl_24415 : CNF.NClause := [(70,true),(20,false),(6,false),(3,true),(17,false),(14,false)]
theorem der_24415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24415 :=
  CNF.rup_sound cl_24415 [cl_546,cl_24407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_546 v h) (hints_cons _ _ _ (der_24407 v h) (by intro d hd; cases hd)))
def cl_24416 : CNF.NClause := [(70,true),(20,false),(6,false),(17,false),(14,true),(28,true)]
theorem der_24416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24416 :=
  CNF.rup_sound cl_24416 [cl_550,cl_23613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_550 v h) (hints_cons _ _ _ (der_23613 v h) (by intro d hd; cases hd)))
def cl_24417 : CNF.NClause := [(70,true),(6,false),(3,true),(14,false),(17,true),(20,false)]
theorem der_24417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24417 :=
  CNF.rup_sound cl_24417 [cl_554,cl_24409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_554 v h) (hints_cons _ _ _ (der_24409 v h) (by intro d hd; cases hd)))
def cl_24418 : CNF.NClause := [(70,true),(20,false),(6,false),(14,true),(17,true),(28,true)]
theorem der_24418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24418 :=
  CNF.rup_sound cl_24418 [cl_558,cl_557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_558 v h) (hints_cons _ _ _ (inp_557 v h) (by intro d hd; cases hd)))
def cl_24419 : CNF.NClause := [(70,true),(14,false),(3,true),(17,false),(20,true),(6,false)]
theorem der_24419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24419 :=
  CNF.rup_sound cl_24419 [cl_562,cl_24411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_562 v h) (hints_cons _ _ _ (der_24411 v h) (by intro d hd; cases hd)))
def cl_24420 : CNF.NClause := [(70,true),(17,false),(6,false),(28,true),(20,true),(14,true)]
theorem der_24420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24420 :=
  CNF.rup_sound cl_24420 [cl_566,cl_23614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_566 v h) (hints_cons _ _ _ (der_23614 v h) (by intro d hd; cases hd)))
def cl_24421 : CNF.NClause := [(70,true),(14,false),(17,true),(3,true),(20,true),(6,false)]
theorem der_24421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24421 :=
  CNF.rup_sound cl_24421 [cl_570,cl_24413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_570 v h) (hints_cons _ _ _ (der_24413 v h) (by intro d hd; cases hd)))
def cl_24422 : CNF.NClause := [(85,true),(12,false),(3,true),(19,false),(21,false),(27,false)]
theorem der_24422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24422 :=
  CNF.rup_sound cl_24422 [cl_1474,cl_24113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1474 v h) (hints_cons _ _ _ (der_24113 v h) (by intro d hd; cases hd)))
def cl_24423 : CNF.NClause := [(85,true),(27,false),(21,false),(3,true),(19,false),(12,true)]
theorem der_24423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24423 :=
  CNF.rup_sound cl_24423 [cl_1478,cl_24285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1478 v h) (hints_cons _ _ _ (der_24285 v h) (by intro d hd; cases hd)))
def cl_24424 : CNF.NClause := [(85,true),(27,false),(21,false),(12,false),(5,false),(3,true)]
theorem der_24424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24424 :=
  CNF.rup_sound cl_24424 [cl_1482,cl_24422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1482 v h) (hints_cons _ _ _ (der_24422 v h) (by intro d hd; cases hd)))
def cl_24425 : CNF.NClause := [(85,true),(27,false),(21,false),(5,false),(19,true),(3,true)]
theorem der_24425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24425 :=
  CNF.rup_sound cl_24425 [cl_1486,cl_24424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1486 v h) (hints_cons _ _ _ (der_24424 v h) (by intro d hd; cases hd)))
def cl_24426 : CNF.NClause := [(85,true),(12,false),(5,false),(19,false),(21,true),(27,false)]
theorem der_24426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24426 :=
  CNF.rup_sound cl_24426 [cl_1490,cl_23648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1490 v h) (hints_cons _ _ _ (der_23648 v h) (by intro d hd; cases hd)))
def cl_24427 : CNF.NClause := [(85,true),(27,false),(5,false),(21,true),(19,false),(12,true)]
theorem der_24427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24427 :=
  CNF.rup_sound cl_24427 [cl_1494,cl_1493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1494 v h) (hints_cons _ _ _ (inp_1493 v h) (by intro d hd; cases hd)))
def cl_24428 : CNF.NClause := [(85,true),(27,false),(5,false),(19,true),(3,true),(12,false)]
theorem der_24428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24428 :=
  CNF.rup_sound cl_24428 [cl_1498,cl_24424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1498 v h) (hints_cons _ _ _ (der_24424 v h) (by intro d hd; cases hd)))
def cl_24429 : CNF.NClause := [(85,true),(27,false),(21,true),(5,false),(12,true),(19,true)]
theorem der_24429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24429 :=
  CNF.rup_sound cl_24429 [cl_1502,cl_23644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1502 v h) (hints_cons _ _ _ (der_23644 v h) (by intro d hd; cases hd)))
def cl_24430 : CNF.NClause := [(85,true),(12,false),(5,false),(19,false),(21,false),(27,true)]
theorem der_24430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24430 :=
  CNF.rup_sound cl_24430 [cl_1506,cl_1505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1506 v h) (hints_cons _ _ _ (inp_1505 v h) (by intro d hd; cases hd)))
def cl_24431 : CNF.NClause := [(85,true),(19,false),(5,false),(3,true),(12,true),(21,false)]
theorem der_24431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24431 :=
  CNF.rup_sound cl_24431 [cl_1510,cl_24423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1510 v h) (hints_cons _ _ _ (der_24423 v h) (by intro d hd; cases hd)))
def cl_24432 : CNF.NClause := [(85,true),(12,false),(5,false),(19,true),(21,false),(3,true)]
theorem der_24432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24432 :=
  CNF.rup_sound cl_24432 [cl_1514,cl_24424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1514 v h) (hints_cons _ _ _ (der_24424 v h) (by intro d hd; cases hd)))
def cl_24433 : CNF.NClause := [(85,true),(27,true),(5,false),(21,false),(12,true),(3,true)]
theorem der_24433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24433 :=
  CNF.rup_sound cl_24433 [cl_1518,cl_24431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1518 v h) (hints_cons _ _ _ (der_24431 v h) (by intro d hd; cases hd)))
def cl_24434 : CNF.NClause := [(85,true),(12,false),(5,false),(19,false),(21,true),(27,true)]
theorem der_24434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24434 :=
  CNF.rup_sound cl_24434 [cl_1522,cl_23649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1522 v h) (hints_cons _ _ _ (der_23649 v h) (by intro d hd; cases hd)))
def cl_24435 : CNF.NClause := [(85,true),(27,true),(5,false),(12,true),(19,false),(21,true)]
theorem der_24435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24435 :=
  CNF.rup_sound cl_24435 [cl_1526,cl_23601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1526 v h) (hints_cons _ _ _ (der_23601 v h) (by intro d hd; cases hd)))
def cl_24436 : CNF.NClause := [(85,true),(27,true),(12,false),(5,false),(19,true),(21,true)]
theorem der_24436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24436 :=
  CNF.rup_sound cl_24436 [cl_1530,cl_23654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1530 v h) (hints_cons _ _ _ (der_23654 v h) (by intro d hd; cases hd)))
def cl_24437 : CNF.NClause := [(75,true),(3,true),(10,false),(16,false),(22,false),(26,false)]
theorem der_24437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24437 :=
  CNF.rup_sound cl_24437 [cl_836,cl_24391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_836 v h) (hints_cons _ _ _ (der_24391 v h) (by intro d hd; cases hd)))
def cl_24438 : CNF.NClause := [(75,true),(9,true),(3,true),(16,false),(22,false),(26,false)]
theorem der_24438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24438 :=
  CNF.rup_sound cl_24438 [cl_840,cl_24437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_840 v h) (hints_cons _ _ _ (der_24437 v h) (by intro d hd; cases hd)))
def cl_24439 : CNF.NClause := [(75,true),(22,false),(3,true),(10,false),(16,true),(26,false)]
theorem der_24439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24439 :=
  CNF.rup_sound cl_24439 [cl_844,cl_842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_844 v h) (hints_cons _ _ _ (inp_842 v h) (by intro d hd; cases hd)))
def cl_24440 : CNF.NClause := [(75,true),(9,true),(3,true),(10,true),(26,false),(22,false)]
theorem der_24440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24440 :=
  CNF.rup_sound cl_24440 [cl_848,cl_24438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_848 v h) (hints_cons _ _ _ (der_24438 v h) (by intro d hd; cases hd)))
def cl_24441 : CNF.NClause := [(75,true),(10,false),(3,true),(16,false),(22,true),(26,false)]
theorem der_24441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24441 :=
  CNF.rup_sound cl_24441 [cl_852,cl_24271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_852 v h) (hints_cons _ _ _ (der_24271 v h) (by intro d hd; cases hd)))
def cl_24442 : CNF.NClause := [(75,true),(9,true),(3,true),(10,true),(16,false),(26,false)]
theorem der_24442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24442 :=
  CNF.rup_sound cl_24442 [cl_856,cl_24440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_856 v h) (hints_cons _ _ _ (der_24440 v h) (by intro d hd; cases hd)))
def cl_24443 : CNF.NClause := [(75,true),(10,false),(3,true),(22,true),(16,true),(26,false)]
theorem der_24443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24443 :=
  CNF.rup_sound cl_24443 [cl_860,cl_23555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_860 v h) (hints_cons _ _ _ (der_23555 v h) (by intro d hd; cases hd)))
def cl_24444 : CNF.NClause := [(75,true),(3,true),(10,false),(16,false),(22,false),(26,true)]
theorem der_24444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24444 :=
  CNF.rup_sound cl_24444 [cl_868,cl_24275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_868 v h) (hints_cons _ _ _ (der_24275 v h) (by intro d hd; cases hd)))
def cl_24445 : CNF.NClause := [(75,true),(9,true),(3,true),(10,true),(16,false),(22,false)]
theorem der_24445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24445 :=
  CNF.rup_sound cl_24445 [cl_872,cl_24440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_872 v h) (hints_cons _ _ _ (der_24440 v h) (by intro d hd; cases hd)))
def cl_24446 : CNF.NClause := [(75,true),(22,false),(3,true),(10,false),(16,true),(26,true)]
theorem der_24446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24446 :=
  CNF.rup_sound cl_24446 [cl_876,cl_23556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_876 v h) (hints_cons _ _ _ (der_23556 v h) (by intro d hd; cases hd)))
def cl_24447 : CNF.NClause := [(75,true),(3,true),(10,false),(16,false),(22,true),(9,true)]
theorem der_24447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24447 :=
  CNF.rup_sound cl_24447 [cl_884,cl_24441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_884 v h) (hints_cons _ _ _ (der_24441 v h) (by intro d hd; cases hd)))
def cl_24448 : CNF.NClause := [(75,true),(10,false),(3,true),(9,false),(22,true),(26,true)]
theorem der_24448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24448 :=
  CNF.rup_sound cl_24448 [cl_882,cl_23557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_882 v h) (hints_cons _ _ _ (der_23557 v h) (by intro d hd; cases hd)))
def cl_24449 : CNF.NClause := [(70,true),(3,true),(6,true),(14,false),(20,false),(17,false)]
theorem der_24449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24449 :=
  CNF.rup_sound cl_24449 [cl_548,cl_24390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_548 v h) (hints_cons _ _ _ (der_24390 v h) (by intro d hd; cases hd)))
def cl_24450 : CNF.NClause := [(80,true),(29,false),(7,true),(15,false),(11,false),(24,false)]
theorem der_24450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24450 :=
  CNF.rup_sound cl_24450 [cl_1156,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1156 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24451 : CNF.NClause := [(70,true),(17,false),(6,false),(3,false),(14,false),(20,false)]
theorem der_24451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24451 :=
  CNF.rup_sound cl_24451 [cl_545,cl_513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_545 v h) (hints_cons _ _ _ (inp_513 v h) (by intro d hd; cases hd)))
def cl_24452 : CNF.NClause := [(81,true),(28,true),(15,false),(9,false),(23,false),(1,true)]
theorem der_24452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24452 :=
  CNF.rup_sound cl_24452 [cl_1254,cl_1250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1254 v h) (hints_cons _ _ _ (inp_1250 v h) (by intro d hd; cases hd)))
def cl_24453 : CNF.NClause := [(84,true),(24,false),(2,false),(13,false),(16,false),(5,false)]
theorem der_24453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24453 :=
  CNF.rup_sound cl_24453 [cl_1441,cl_23616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1441 v h) (hints_cons _ _ _ (der_23616 v h) (by intro d hd; cases hd)))
def cl_24454 : CNF.NClause := [(86,true),(29,true),(14,false),(18,false),(5,true),(22,true)]
theorem der_24454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24454 :=
  CNF.rup_sound cl_24454 [cl_1588,cl_24073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1588 v h) (hints_cons _ _ _ (der_24073 v h) (by intro d hd; cases hd)))
def cl_24455 : CNF.NClause := [(86,true),(1,false),(18,false),(29,true),(14,false),(22,true)]
theorem der_24455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24455 :=
  CNF.rup_sound cl_24455 [cl_1585,cl_24454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1585 v h) (hints_cons _ _ _ (der_24454 v h) (by intro d hd; cases hd)))
def cl_24456 : CNF.NClause := [(73,true),(28,true),(10,false),(7,true),(21,true),(18,false)]
theorem der_24456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24456 :=
  CNF.rup_sound cl_24456 [cl_756,cl_23646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_756 v h) (hints_cons _ _ _ (der_23646 v h) (by intro d hd; cases hd)))
def cl_24457 : CNF.NClause := [(73,true),(10,false),(4,false),(7,false),(21,true),(18,false)]
theorem der_24457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24457 :=
  CNF.rup_sound cl_24457 [cl_753,cl_23262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_753 v h) (hints_cons _ _ _ (der_23262 v h) (by intro d hd; cases hd)))
def cl_24458 : CNF.NClause := [(74,true),(29,false),(2,false),(6,false),(23,false),(19,false)]
theorem der_24458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24458 :=
  CNF.rup_sound cl_24458 [cl_773,cl_769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_773 v h) (hints_cons _ _ _ (inp_769 v h) (by intro d hd; cases hd)))
def cl_24459 : CNF.NClause := [(74,true),(29,false),(2,false),(19,true),(10,true),(23,false)]
theorem der_24459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24459 :=
  CNF.rup_sound cl_24459 [cl_781,cl_24009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_781 v h) (hints_cons _ _ _ (der_24009 v h) (by intro d hd; cases hd)))
def cl_24460 : CNF.NClause := [(74,true),(29,false),(2,false),(6,false),(10,true),(19,false)]
theorem der_24460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24460 :=
  CNF.rup_sound cl_24460 [cl_789,cl_24458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_789 v h) (hints_cons _ _ _ (der_24458 v h) (by intro d hd; cases hd)))
def cl_24461 : CNF.NClause := [(74,true),(29,false),(6,false),(10,true),(19,true),(23,true)]
theorem der_24461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24461 :=
  CNF.rup_sound cl_24461 [cl_797,cl_23523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_797 v h) (hints_cons _ _ _ (der_23523 v h) (by intro d hd; cases hd)))
def cl_24462 : CNF.NClause := [(74,true),(29,true),(6,false),(10,true),(19,false),(23,false)]
theorem der_24462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24462 :=
  CNF.rup_sound cl_24462 [cl_805,cl_23524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_805 v h) (hints_cons _ _ _ (der_23524 v h) (by intro d hd; cases hd)))
def cl_24463 : CNF.NClause := [(74,true),(29,true),(6,false),(10,true),(19,true),(23,false)]
theorem der_24463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24463 :=
  CNF.rup_sound cl_24463 [cl_813,cl_23526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_813 v h) (hints_cons _ _ _ (der_23526 v h) (by intro d hd; cases hd)))
def cl_24464 : CNF.NClause := [(74,true),(29,true),(2,false),(6,false),(19,false),(23,true)]
theorem der_24464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24464 :=
  CNF.rup_sound cl_24464 [cl_821,cl_24266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_821 v h) (hints_cons _ _ _ (der_24266 v h) (by intro d hd; cases hd)))
def cl_24465 : CNF.NClause := [(74,true),(2,false),(6,false),(10,true),(19,true),(23,true)]
theorem der_24465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24465 :=
  CNF.rup_sound cl_24465 [cl_829,cl_24461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_829 v h) (hints_cons _ _ _ (der_24461 v h) (by intro d hd; cases hd)))
def cl_24466 : CNF.NClause := [(73,true),(28,false),(4,false),(7,false),(21,false),(18,false)]
theorem der_24466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24466 :=
  CNF.rup_sound cl_24466 [cl_709,cl_23499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_709 v h) (hints_cons _ _ _ (der_23499 v h) (by intro d hd; cases hd)))
def cl_24467 : CNF.NClause := [(73,true),(28,false),(21,false),(7,false),(4,false),(10,true)]
theorem der_24467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24467 :=
  CNF.rup_sound cl_24467 [cl_717,cl_24466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_717 v h) (hints_cons _ _ _ (der_24466 v h) (by intro d hd; cases hd)))
def cl_24468 : CNF.NClause := [(73,true),(28,false),(4,false),(7,false),(18,false),(21,true)]
theorem der_24468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24468 :=
  CNF.rup_sound cl_24468 [cl_725,cl_23262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_725 v h) (hints_cons _ _ _ (der_23262 v h) (by intro d hd; cases hd)))
def cl_24469 : CNF.NClause := [(73,true),(28,false),(4,false),(7,false),(18,true),(21,true)]
theorem der_24469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24469 :=
  CNF.rup_sound cl_24469 [cl_733,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_733 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_24470 : CNF.NClause := [(73,true),(21,false),(4,false),(7,false),(10,true),(18,false)]
theorem der_24470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24470 :=
  CNF.rup_sound cl_24470 [cl_741,cl_24466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_741 v h) (hints_cons _ _ _ (der_24466 v h) (by intro d hd; cases hd)))
def cl_24471 : CNF.NClause := [(73,true),(18,true),(4,false),(7,false),(10,true),(21,false)]
theorem der_24471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24471 :=
  CNF.rup_sound cl_24471 [cl_749,cl_24467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_749 v h) (hints_cons _ _ _ (der_24467 v h) (by intro d hd; cases hd)))
def cl_24472 : CNF.NClause := [(73,true),(21,true),(7,false),(18,false),(10,true),(28,true)]
theorem der_24472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24472 :=
  CNF.rup_sound cl_24472 [cl_757,cl_23548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_757 v h) (hints_cons _ _ _ (der_23548 v h) (by intro d hd; cases hd)))
def cl_24473 : CNF.NClause := [(73,true),(4,false),(7,false),(18,true),(10,true),(21,true)]
theorem der_24473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24473 :=
  CNF.rup_sound cl_24473 [cl_765,cl_24469] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_765 v h) (hints_cons _ _ _ (der_24469 v h) (by intro d hd; cases hd)))
def cl_24474 : CNF.NClause := [(76,true),(24,false),(1,false),(8,false),(17,false),(27,false)]
theorem der_24474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24474 :=
  CNF.rup_sound cl_24474 [cl_901,cl_23610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_901 v h) (hints_cons _ _ _ (der_23610 v h) (by intro d hd; cases hd)))
def cl_24475 : CNF.NClause := [(76,true),(27,false),(8,false),(10,true),(17,true),(24,false)]
theorem der_24475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24475 :=
  CNF.rup_sound cl_24475 [cl_909,cl_24195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_909 v h) (hints_cons _ _ _ (der_24195 v h) (by intro d hd; cases hd)))
def cl_24476 : CNF.NClause := [(76,true),(27,false),(17,false),(8,false),(24,true),(1,false)]
theorem der_24476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24476 :=
  CNF.rup_sound cl_24476 [cl_917,cl_24310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_917 v h) (hints_cons _ _ _ (der_24310 v h) (by intro d hd; cases hd)))
def cl_24477 : CNF.NClause := [(76,true),(27,false),(1,false),(8,false),(10,true),(17,true)]
theorem der_24477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24477 :=
  CNF.rup_sound cl_24477 [cl_925,cl_24475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_925 v h) (hints_cons _ _ _ (der_24475 v h) (by intro d hd; cases hd)))
def cl_24478 : CNF.NClause := [(76,true),(24,false),(1,false),(8,false),(17,false),(27,true)]
theorem der_24478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24478 :=
  CNF.rup_sound cl_24478 [cl_933,cl_929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_933 v h) (hints_cons _ _ _ (inp_929 v h) (by intro d hd; cases hd)))
def cl_24479 : CNF.NClause := [(76,true),(1,false),(8,false),(10,true),(17,true),(24,false)]
theorem der_24479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24479 :=
  CNF.rup_sound cl_24479 [cl_941,cl_24475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_941 v h) (hints_cons _ _ _ (der_24475 v h) (by intro d hd; cases hd)))
def cl_24480 : CNF.NClause := [(76,true),(17,false),(1,false),(8,false),(10,true),(27,true)]
theorem der_24480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24480 :=
  CNF.rup_sound cl_24480 [cl_949,cl_24478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_949 v h) (hints_cons _ _ _ (der_24478 v h) (by intro d hd; cases hd)))
def cl_24481 : CNF.NClause := [(76,true),(27,true),(8,false),(10,true),(24,true),(1,false)]
theorem der_24481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24481 :=
  CNF.rup_sound cl_24481 [cl_957,cl_24480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_957 v h) (hints_cons _ _ _ (der_24480 v h) (by intro d hd; cases hd)))
def cl_24482 : CNF.NClause := [(75,true),(26,false),(3,false),(9,false),(16,false),(22,false)]
theorem der_24482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24482 :=
  CNF.rup_sound cl_24482 [cl_837,cl_833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_837 v h) (hints_cons _ _ _ (inp_833 v h) (by intro d hd; cases hd)))
def cl_24483 : CNF.NClause := [(75,true),(22,false),(9,false),(10,true),(16,true),(26,false)]
theorem der_24483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24483 :=
  CNF.rup_sound cl_24483 [cl_845,cl_23565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_845 v h) (hints_cons _ _ _ (der_23565 v h) (by intro d hd; cases hd)))
def cl_24484 : CNF.NClause := [(75,true),(26,false),(9,false),(3,false),(10,true),(16,false)]
theorem der_24484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24484 :=
  CNF.rup_sound cl_24484 [cl_853,cl_24482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_853 v h) (hints_cons _ _ _ (der_24482 v h) (by intro d hd; cases hd)))
def cl_24485 : CNF.NClause := [(75,true),(3,false),(22,true),(9,false),(16,true),(26,false)]
theorem der_24485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24485 :=
  CNF.rup_sound cl_24485 [cl_861,cl_23637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_861 v h) (hints_cons _ _ _ (der_23637 v h) (by intro d hd; cases hd)))
def cl_24486 : CNF.NClause := [(75,true),(26,true),(22,false),(3,false),(16,false),(9,false)]
theorem der_24486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24486 :=
  CNF.rup_sound cl_24486 [cl_869,cl_24276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_869 v h) (hints_cons _ _ _ (der_24276 v h) (by intro d hd; cases hd)))
def cl_24487 : CNF.NClause := [(75,true),(26,true),(22,false),(3,false),(16,true),(9,false)]
theorem der_24487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24487 :=
  CNF.rup_sound cl_24487 [cl_877,cl_23558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_877 v h) (hints_cons _ _ _ (der_23558 v h) (by intro d hd; cases hd)))
def cl_24488 : CNF.NClause := [(75,true),(26,true),(9,false),(3,false),(16,false),(22,true)]
theorem der_24488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24488 :=
  CNF.rup_sound cl_24488 [cl_885,cl_24273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_885 v h) (hints_cons _ _ _ (der_24273 v h) (by intro d hd; cases hd)))
def cl_24489 : CNF.NClause := [(75,true),(16,true),(22,true),(3,false),(26,true),(9,false)]
theorem der_24489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24489 :=
  CNF.rup_sound cl_24489 [cl_893,cl_23559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_893 v h) (hints_cons _ _ _ (der_23559 v h) (by intro d hd; cases hd)))
def cl_24490 : CNF.NClause := [(74,true),(23,false),(2,true),(6,true),(29,false),(19,false)]
theorem der_24490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24490 :=
  CNF.rup_sound cl_24490 [cl_776,cl_24040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_776 v h) (hints_cons _ _ _ (der_24040 v h) (by intro d hd; cases hd)))
def cl_24491 : CNF.NClause := [(74,true),(29,false),(2,true),(6,true),(23,true),(19,false)]
theorem der_24491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24491 :=
  CNF.rup_sound cl_24491 [cl_792,cl_24042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_792 v h) (hints_cons _ _ _ (der_24042 v h) (by intro d hd; cases hd)))
def cl_24492 : CNF.NClause := [(74,true),(29,true),(2,true),(10,true),(19,false),(23,false)]
theorem der_24492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24492 :=
  CNF.rup_sound cl_24492 [cl_808,cl_23524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_808 v h) (hints_cons _ _ _ (der_23524 v h) (by intro d hd; cases hd)))
def cl_24493 : CNF.NClause := [(73,true),(28,false),(21,false),(18,false),(4,false),(7,true)]
theorem der_24493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24493 :=
  CNF.rup_sound cl_24493 [cl_711,cl_23499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_711 v h) (hints_cons _ _ _ (der_23499 v h) (by intro d hd; cases hd)))
def cl_24494 : CNF.NClause := [(73,true),(28,false),(4,false),(7,true),(21,true),(18,false)]
theorem der_24494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24494 :=
  CNF.rup_sound cl_24494 [cl_727,cl_23262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_727 v h) (hints_cons _ _ _ (der_23262 v h) (by intro d hd; cases hd)))
def cl_24495 : CNF.NClause := [(73,true),(4,false),(7,true),(10,true),(21,false),(18,false)]
theorem der_24495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24495 :=
  CNF.rup_sound cl_24495 [cl_743,cl_24493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_743 v h) (hints_cons _ _ _ (der_24493 v h) (by intro d hd; cases hd)))
def cl_24496 : CNF.NClause := [(73,true),(21,true),(4,false),(7,true),(18,false),(28,true)]
theorem der_24496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24496 :=
  CNF.rup_sound cl_24496 [cl_759,cl_23646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_759 v h) (hints_cons _ _ _ (der_23646 v h) (by intro d hd; cases hd)))
def cl_24497 : CNF.NClause := [(75,true),(22,false),(3,true),(9,false),(26,false),(16,false)]
theorem der_24497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24497 :=
  CNF.rup_sound cl_24497 [cl_838,cl_24391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_838 v h) (hints_cons _ _ _ (der_24391 v h) (by intro d hd; cases hd)))
def cl_24498 : CNF.NClause := [(75,true),(22,true),(3,true),(9,false),(26,false),(16,false)]
theorem der_24498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24498 :=
  CNF.rup_sound cl_24498 [cl_854,cl_24271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_854 v h) (hints_cons _ _ _ (der_24271 v h) (by intro d hd; cases hd)))
def cl_24499 : CNF.NClause := [(75,true),(22,false),(3,true),(10,true),(26,true),(9,false)]
theorem der_24499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24499 :=
  CNF.rup_sound cl_24499 [cl_870,cl_23566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_870 v h) (hints_cons _ _ _ (der_23566 v h) (by intro d hd; cases hd)))
def cl_24500 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(26,true)]
theorem der_24500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24500 :=
  CNF.rup_sound cl_24500 [cl_886,cl_24499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_886 v h) (hints_cons _ _ _ (der_24499 v h) (by intro d hd; cases hd)))
def cl_24501 : CNF.NClause := [(74,true),(19,true),(6,true),(10,true),(23,false),(29,false)]
theorem der_24501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24501 :=
  CNF.rup_sound cl_24501 [cl_784,cl_24009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_784 v h) (hints_cons _ _ _ (der_24009 v h) (by intro d hd; cases hd)))
def cl_24502 : CNF.NClause := [(73,true),(4,true),(28,false),(10,true),(18,false),(21,false)]
theorem der_24502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24502 :=
  CNF.rup_sound cl_24502 [cl_712,cl_23536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_712 v h) (hints_cons _ _ _ (der_23536 v h) (by intro d hd; cases hd)))
def cl_24503 : CNF.NClause := [(73,true),(28,false),(18,true),(10,true),(4,true),(21,false)]
theorem der_24503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24503 :=
  CNF.rup_sound cl_24503 [cl_720,cl_23538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_720 v h) (hints_cons _ _ _ (der_23538 v h) (by intro d hd; cases hd)))
def cl_24504 : CNF.NClause := [(73,true),(4,true),(28,false),(10,true),(18,false),(21,true)]
theorem der_24504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24504 :=
  CNF.rup_sound cl_24504 [cl_728,cl_23540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_728 v h) (hints_cons _ _ _ (der_23540 v h) (by intro d hd; cases hd)))
def cl_24505 : CNF.NClause := [(73,true),(18,false),(28,true),(7,true),(10,true),(21,false)]
theorem der_24505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24505 :=
  CNF.rup_sound cl_24505 [cl_744,cl_24495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_744 v h) (hints_cons _ _ _ (der_24495 v h) (by intro d hd; cases hd)))
def cl_24506 : CNF.NClause := [(75,true),(26,false),(9,true),(10,true),(16,false),(22,false)]
theorem der_24506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24506 :=
  CNF.rup_sound cl_24506 [cl_839,cl_24445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_839 v h) (hints_cons _ _ _ (der_24445 v h) (by intro d hd; cases hd)))
def cl_24507 : CNF.NClause := [(75,true),(9,true),(26,false),(3,false),(22,false),(10,true)]
theorem der_24507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24507 :=
  CNF.rup_sound cl_24507 [cl_847,cl_24506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_847 v h) (hints_cons _ _ _ (der_24506 v h) (by intro d hd; cases hd)))
def cl_24508 : CNF.NClause := [(75,true),(26,false),(9,true),(3,false),(10,true),(16,false)]
theorem der_24508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24508 :=
  CNF.rup_sound cl_24508 [cl_855,cl_24506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_855 v h) (hints_cons _ _ _ (der_24506 v h) (by intro d hd; cases hd)))
def cl_24509 : CNF.NClause := [(75,true),(26,false),(22,true),(16,true),(10,true),(3,false)]
theorem der_24509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24509 :=
  CNF.rup_sound cl_24509 [cl_863,cl_24485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_863 v h) (hints_cons _ _ _ (der_24485 v h) (by intro d hd; cases hd)))
def cl_24510 : CNF.NClause := [(75,true),(26,true),(9,true),(10,true),(16,false),(22,false)]
theorem der_24510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24510 :=
  CNF.rup_sound cl_24510 [cl_871,cl_24445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_871 v h) (hints_cons _ _ _ (der_24445 v h) (by intro d hd; cases hd)))
def cl_24511 : CNF.NClause := [(75,true),(9,true),(3,false),(16,true),(22,false),(26,true)]
theorem der_24511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24511 :=
  CNF.rup_sound cl_24511 [cl_879,cl_23572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_879 v h) (hints_cons _ _ _ (der_23572 v h) (by intro d hd; cases hd)))
def cl_24512 : CNF.NClause := [(74,true),(23,false),(2,true),(6,false),(10,true),(19,false)]
theorem der_24512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24512 :=
  CNF.rup_sound cl_24512 [cl_774,cl_23524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_774 v h) (hints_cons _ _ _ (der_23524 v h) (by intro d hd; cases hd)))
def cl_24513 : CNF.NClause := [(74,true),(2,true),(6,false),(10,true),(19,true),(29,false)]
theorem der_24513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24513 :=
  CNF.rup_sound cl_24513 [cl_782,cl_23523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_782 v h) (hints_cons _ _ _ (der_23523 v h) (by intro d hd; cases hd)))
def cl_24514 : CNF.NClause := [(74,true),(29,false),(2,true),(6,false),(10,true),(23,true)]
theorem der_24514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24514 :=
  CNF.rup_sound cl_24514 [cl_790,cl_23523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_790 v h) (hints_cons _ _ _ (der_23523 v h) (by intro d hd; cases hd)))
def cl_24515 : CNF.NClause := [(76,true),(24,false),(8,true),(1,false),(17,false),(27,false)]
theorem der_24515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24515 :=
  CNF.rup_sound cl_24515 [cl_903,cl_23990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_903 v h) (hints_cons _ _ _ (der_23990 v h) (by intro d hd; cases hd)))
def cl_24516 : CNF.NClause := [(76,true),(27,false),(1,false),(10,true),(17,true),(24,false)]
theorem der_24516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24516 :=
  CNF.rup_sound cl_24516 [cl_911,cl_24475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_911 v h) (hints_cons _ _ _ (der_24475 v h) (by intro d hd; cases hd)))
def cl_24517 : CNF.NClause := [(76,true),(8,true),(17,false),(1,false),(24,true),(27,false)]
theorem der_24517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24517 :=
  CNF.rup_sound cl_24517 [cl_919,cl_24314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_919 v h) (hints_cons _ _ _ (der_24314 v h) (by intro d hd; cases hd)))
def cl_24518 : CNF.NClause := [(76,true),(8,true),(1,false),(10,true),(24,true),(27,false)]
theorem der_24518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24518 :=
  CNF.rup_sound cl_24518 [cl_927,cl_24517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_927 v h) (hints_cons _ _ _ (der_24517 v h) (by intro d hd; cases hd)))
def cl_24519 : CNF.NClause := [(78,true),(27,false),(22,false),(6,false),(15,false),(13,false)]
theorem der_24519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24519 :=
  CNF.rup_sound cl_24519 [cl_1026,cl_1025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1026 v h) (hints_cons _ _ _ (inp_1025 v h) (by intro d hd; cases hd)))
def cl_24520 : CNF.NClause := [(78,true),(27,false),(6,false),(22,true),(13,false),(15,false)]
theorem der_24520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24520 :=
  CNF.rup_sound cl_24520 [cl_1042,cl_23632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1042 v h) (hints_cons _ _ _ (der_23632 v h) (by intro d hd; cases hd)))
def cl_24521 : CNF.NClause := [(78,true),(22,true),(6,false),(13,false),(15,false),(27,true)]
theorem der_24521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24521 :=
  CNF.rup_sound cl_24521 [cl_1074,cl_1073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1074 v h) (hints_cons _ _ _ (inp_1073 v h) (by intro d hd; cases hd)))
def cl_24522 : CNF.NClause := [(78,true),(6,false),(4,true),(15,false),(22,true),(27,true)]
theorem der_24522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24522 :=
  CNF.rup_sound cl_24522 [cl_1078,cl_24521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1078 v h) (hints_cons _ _ _ (der_24521 v h) (by intro d hd; cases hd)))
def cl_24523 : CNF.NClause := [(78,true),(27,true),(6,false),(4,true),(13,false),(22,true)]
theorem der_24523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24523 :=
  CNF.rup_sound cl_24523 [cl_1082,cl_24522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1082 v h) (hints_cons _ _ _ (der_24522 v h) (by intro d hd; cases hd)))
def cl_24524 : CNF.NClause := [(68,true),(4,true),(12,false),(16,false),(20,false),(29,false)]
theorem der_24524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24524 :=
  CNF.rup_sound cl_24524 [cl_386,cl_23985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_386 v h) (hints_cons _ _ _ (der_23985 v h) (by intro d hd; cases hd)))
def cl_24525 : CNF.NClause := [(68,true),(8,false),(12,true),(16,false),(20,false),(29,false)]
theorem der_24525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24525 :=
  CNF.rup_sound cl_24525 [cl_390,cl_389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_390 v h) (hints_cons _ _ _ (inp_389 v h) (by intro d hd; cases hd)))
def cl_24526 : CNF.NClause := [(68,true),(8,false),(12,false),(4,true),(20,false),(29,false)]
theorem der_24526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24526 :=
  CNF.rup_sound cl_24526 [cl_394,cl_24524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_394 v h) (hints_cons _ _ _ (der_24524 v h) (by intro d hd; cases hd)))
def cl_24527 : CNF.NClause := [(68,true),(8,false),(12,true),(16,true),(20,false),(29,false)]
theorem der_24527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24527 :=
  CNF.rup_sound cl_24527 [cl_398,cl_23515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_398 v h) (hints_cons _ _ _ (der_23515 v h) (by intro d hd; cases hd)))
def cl_24528 : CNF.NClause := [(68,true),(29,false),(4,true),(16,false),(8,false),(12,false)]
theorem der_24528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24528 :=
  CNF.rup_sound cl_24528 [cl_402,cl_24524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_402 v h) (hints_cons _ _ _ (der_24524 v h) (by intro d hd; cases hd)))
def cl_24529 : CNF.NClause := [(68,true),(29,false),(8,false),(12,true),(20,true),(16,false)]
theorem der_24529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24529 :=
  CNF.rup_sound cl_24529 [cl_406,cl_23516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_406 v h) (hints_cons _ _ _ (der_23516 v h) (by intro d hd; cases hd)))
def cl_24530 : CNF.NClause := [(68,true),(29,false),(8,false),(12,false),(4,true),(16,true)]
theorem der_24530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24530 :=
  CNF.rup_sound cl_24530 [cl_410,cl_24526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_410 v h) (hints_cons _ _ _ (der_24526 v h) (by intro d hd; cases hd)))
def cl_24531 : CNF.NClause := [(68,true),(29,false),(8,false),(12,true),(20,true),(16,true)]
theorem der_24531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24531 :=
  CNF.rup_sound cl_24531 [cl_414,cl_23517] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_414 v h) (hints_cons _ _ _ (der_23517 v h) (by intro d hd; cases hd)))
def cl_24532 : CNF.NClause := [(68,true),(4,true),(12,false),(16,false),(20,false),(29,true)]
theorem der_24532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24532 :=
  CNF.rup_sound cl_24532 [cl_418,cl_24000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_418 v h) (hints_cons _ _ _ (der_24000 v h) (by intro d hd; cases hd)))
def cl_24533 : CNF.NClause := [(68,true),(8,false),(12,true),(16,false),(20,false),(29,true)]
theorem der_24533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24533 :=
  CNF.rup_sound cl_24533 [cl_422,cl_23518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_422 v h) (hints_cons _ _ _ (der_23518 v h) (by intro d hd; cases hd)))
def cl_24534 : CNF.NClause := [(68,true),(16,true),(8,false),(12,false),(4,true),(20,false)]
theorem der_24534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24534 :=
  CNF.rup_sound cl_24534 [cl_426,cl_24526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_426 v h) (hints_cons _ _ _ (der_24526 v h) (by intro d hd; cases hd)))
def cl_24535 : CNF.NClause := [(68,true),(8,false),(12,true),(16,true),(20,false),(29,true)]
theorem der_24535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24535 :=
  CNF.rup_sound cl_24535 [cl_430,cl_23519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_430 v h) (hints_cons _ _ _ (der_23519 v h) (by intro d hd; cases hd)))
def cl_24536 : CNF.NClause := [(68,true),(20,true),(12,false),(16,false),(8,false),(29,true)]
theorem der_24536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24536 :=
  CNF.rup_sound cl_24536 [cl_434,cl_24168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_434 v h) (hints_cons _ _ _ (der_24168 v h) (by intro d hd; cases hd)))
def cl_24537 : CNF.NClause := [(68,true),(20,true),(12,true),(16,false),(8,false),(29,true)]
theorem der_24537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24537 :=
  CNF.rup_sound cl_24537 [cl_438,cl_23520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_438 v h) (hints_cons _ _ _ (der_23520 v h) (by intro d hd; cases hd)))
def cl_24538 : CNF.NClause := [(68,true),(8,false),(12,false),(4,true),(20,true),(16,true)]
theorem der_24538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24538 :=
  CNF.rup_sound cl_24538 [cl_442,cl_24530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_442 v h) (hints_cons _ _ _ (der_24530 v h) (by intro d hd; cases hd)))
def cl_24539 : CNF.NClause := [(83,true),(17,false),(23,false),(5,false),(26,false),(4,true)]
theorem der_24539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24539 :=
  CNF.rup_sound cl_24539 [cl_1346,cl_1350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1346 v h) (hints_cons _ _ _ (inp_1350 v h) (by intro d hd; cases hd)))
def cl_24540 : CNF.NClause := [(83,true),(17,false),(26,false),(5,false),(4,true),(23,true)]
theorem der_24540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24540 :=
  CNF.rup_sound cl_24540 [cl_1362,cl_23531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1362 v h) (hints_cons _ _ _ (der_23531 v h) (by intro d hd; cases hd)))
def cl_24541 : CNF.NClause := [(83,true),(17,false),(26,true),(11,false),(4,true),(5,false)]
theorem der_24541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24541 :=
  CNF.rup_sound cl_24541 [cl_1394,cl_1378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1394 v h) (hints_cons _ _ _ (inp_1378 v h) (by intro d hd; cases hd)))
def cl_24542 : CNF.NClause := [(83,true),(17,false),(11,true),(23,true),(4,true),(5,false)]
theorem der_24542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24542 :=
  CNF.rup_sound cl_24542 [cl_1398,cl_23531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1398 v h) (hints_cons _ _ _ (der_23531 v h) (by intro d hd; cases hd)))
def cl_24543 : CNF.NClause := [(83,true),(23,true),(11,false),(26,true),(4,true),(5,false)]
theorem der_24543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24543 :=
  CNF.rup_sound cl_24543 [cl_1402,cl_24541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1402 v h) (hints_cons _ _ _ (der_24541 v h) (by intro d hd; cases hd)))
def cl_24544 : CNF.NClause := [(74,true),(10,false),(19,true),(6,false),(23,false),(29,false)]
theorem der_24544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24544 :=
  CNF.rup_sound cl_24544 [cl_777,cl_23552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_777 v h) (hints_cons _ _ _ (der_23552 v h) (by intro d hd; cases hd)))
def cl_24545 : CNF.NClause := [(74,true),(10,false),(23,true),(6,false),(19,true),(29,false)]
theorem der_24545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24545 :=
  CNF.rup_sound cl_24545 [cl_793,cl_794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_793 v h) (hints_cons _ _ _ (inp_794 v h) (by intro d hd; cases hd)))
def cl_24546 : CNF.NClause := [(74,true),(23,false),(6,false),(19,true),(10,false),(29,true)]
theorem der_24546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24546 :=
  CNF.rup_sound cl_24546 [cl_809,cl_23525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_809 v h) (hints_cons _ _ _ (der_23525 v h) (by intro d hd; cases hd)))
def cl_24547 : CNF.NClause := [(74,true),(23,true),(2,false),(6,false),(10,false),(29,true)]
theorem der_24547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24547 :=
  CNF.rup_sound cl_24547 [cl_825,cl_24266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_825 v h) (hints_cons _ _ _ (der_24266 v h) (by intro d hd; cases hd)))
def cl_24548 : CNF.NClause := [(86,true),(18,false),(1,false),(5,false),(22,false),(29,false)]
theorem der_24548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24548 :=
  CNF.rup_sound cl_24548 [cl_1537,cl_1541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1537 v h) (hints_cons _ _ _ (inp_1541 v h) (by intro d hd; cases hd)))
def cl_24549 : CNF.NClause := [(70,true),(20,false),(6,true),(14,false),(17,true),(28,false)]
theorem der_24549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24549 :=
  CNF.rup_sound cl_24549 [cl_524,cl_24027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_524 v h) (hints_cons _ _ _ (der_24027 v h) (by intro d hd; cases hd)))
def cl_24550 : CNF.NClause := [(70,true),(6,true),(3,true),(28,false),(14,false),(20,true)]
theorem der_24550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24550 :=
  CNF.rup_sound cl_24550 [cl_540,cl_24169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_540 v h) (hints_cons _ _ _ (der_24169 v h) (by intro d hd; cases hd)))
def cl_24551 : CNF.NClause := [(70,true),(20,false),(6,true),(28,true),(17,true),(14,false)]
theorem der_24551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24551 :=
  CNF.rup_sound cl_24551 [cl_556,cl_24027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_556 v h) (hints_cons _ _ _ (der_24027 v h) (by intro d hd; cases hd)))
def cl_24552 : CNF.NClause := [(86,true),(14,false),(1,true),(22,false),(5,true),(29,false)]
theorem der_24552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24552 :=
  CNF.rup_sound cl_24552 [cl_1548,cl_24189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1548 v h) (hints_cons _ _ _ (der_24189 v h) (by intro d hd; cases hd)))
def cl_24553 : CNF.NClause := [(86,true),(22,true),(1,true),(14,false),(18,true),(29,false)]
theorem der_24553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24553 :=
  CNF.rup_sound cl_24553 [cl_1564,cl_24228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1564 v h) (hints_cons _ _ _ (der_24228 v h) (by intro d hd; cases hd)))
def cl_24554 : CNF.NClause := [(86,true),(29,true),(1,true),(14,false),(22,false),(18,true)]
theorem der_24554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24554 :=
  CNF.rup_sound cl_24554 [cl_1580,cl_24232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1580 v h) (hints_cons _ _ _ (der_24232 v h) (by intro d hd; cases hd)))
def cl_24555 : CNF.NClause := [(86,true),(1,false),(5,false),(22,false),(18,true),(29,false)]
theorem der_24555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24555 :=
  CNF.rup_sound cl_24555 [cl_1545,cl_23608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1545 v h) (hints_cons _ _ _ (der_23608 v h) (by intro d hd; cases hd)))
def cl_24556 : CNF.NClause := [(86,true),(1,false),(29,false),(5,false),(18,true),(22,true)]
theorem der_24556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24556 :=
  CNF.rup_sound cl_24556 [cl_1561,cl_23609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1561 v h) (hints_cons _ _ _ (der_23609 v h) (by intro d hd; cases hd)))
def cl_24557 : CNF.NClause := [(86,true),(5,false),(1,false),(18,true),(22,false),(29,true)]
theorem der_24557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24557 :=
  CNF.rup_sound cl_24557 [cl_1577,cl_1581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1577 v h) (hints_cons _ _ _ (inp_1581 v h) (by intro d hd; cases hd)))
def cl_24558 : CNF.NClause := [(86,true),(5,false),(1,false),(18,true),(22,true),(29,true)]
theorem der_24558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24558 :=
  CNF.rup_sound cl_24558 [cl_1593,cl_23588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1593 v h) (hints_cons _ _ _ (der_23588 v h) (by intro d hd; cases hd)))
def cl_24559 : CNF.NClause := [(86,true),(18,false),(22,true),(1,false),(5,false),(29,false)]
theorem der_24559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24559 :=
  CNF.rup_sound cl_24559 [cl_1553,cl_23607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1553 v h) (hints_cons _ _ _ (der_23607 v h) (by intro d hd; cases hd)))
def cl_24560 : CNF.NClause := [(76,true),(27,false),(1,true),(10,true),(17,true),(24,false)]
theorem der_24560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24560 :=
  CNF.rup_sound cl_24560 [cl_912,cl_24475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_912 v h) (hints_cons _ _ _ (der_24475 v h) (by intro d hd; cases hd)))
def cl_24561 : CNF.NClause := [(83,true),(4,false),(5,true),(23,false),(17,true),(26,false)]
theorem der_24561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24561 :=
  CNF.rup_sound cl_24561 [cl_1359,cl_24125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1359 v h) (hints_cons _ _ _ (der_24125 v h) (by intro d hd; cases hd)))
def cl_24562 : CNF.NClause := [(83,true),(4,false),(17,true),(5,true),(23,true),(26,false)]
theorem der_24562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24562 :=
  CNF.rup_sound cl_24562 [cl_1375,cl_24123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1375 v h) (hints_cons _ _ _ (der_24123 v h) (by intro d hd; cases hd)))
def cl_24563 : CNF.NClause := [(83,true),(23,false),(4,false),(5,true),(17,true),(26,true)]
theorem der_24563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24563 :=
  CNF.rup_sound cl_24563 [cl_1391,cl_24125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1391 v h) (hints_cons _ _ _ (der_24125 v h) (by intro d hd; cases hd)))
def cl_24564 : CNF.NClause := [(76,true),(27,false),(1,false),(8,false),(10,false),(24,false)]
theorem der_24564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24564 :=
  CNF.rup_sound cl_24564 [cl_905,cl_23610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_905 v h) (hints_cons _ _ _ (der_23610 v h) (by intro d hd; cases hd)))
def cl_24565 : CNF.NClause := [(76,true),(10,false),(8,false),(17,true),(24,true),(27,false)]
theorem der_24565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24565 :=
  CNF.rup_sound cl_24565 [cl_921,cl_24198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_921 v h) (hints_cons _ _ _ (der_24198 v h) (by intro d hd; cases hd)))
def cl_24566 : CNF.NClause := [(76,true),(27,true),(1,false),(8,false),(10,false),(24,false)]
theorem der_24566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24566 :=
  CNF.rup_sound cl_24566 [cl_937,cl_929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_937 v h) (hints_cons _ _ _ (inp_929 v h) (by intro d hd; cases hd)))
def cl_24567 : CNF.NClause := [(76,true),(1,false),(8,false),(17,true),(24,true),(27,true)]
theorem der_24567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24567 :=
  CNF.rup_sound cl_24567 [cl_953,cl_24481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_953 v h) (hints_cons _ _ _ (der_24481 v h) (by intro d hd; cases hd)))
def cl_24568 : CNF.NClause := [(83,true),(23,false),(4,false),(5,false),(26,false),(11,false)]
theorem der_24568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24568 :=
  CNF.rup_sound cl_24568 [cl_1353,cl_23611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1353 v h) (hints_cons _ _ _ (der_23611 v h) (by intro d hd; cases hd)))
def cl_24569 : CNF.NClause := [(83,true),(23,true),(4,false),(5,false),(26,false),(11,false)]
theorem der_24569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24569 :=
  CNF.rup_sound cl_24569 [cl_1369,cl_24263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1369 v h) (hints_cons _ _ _ (der_24263 v h) (by intro d hd; cases hd)))
def cl_24570 : CNF.NClause := [(83,true),(23,false),(11,false),(26,true),(4,false),(5,false)]
theorem der_24570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24570 :=
  CNF.rup_sound cl_24570 [cl_1385,cl_23611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1385 v h) (hints_cons _ _ _ (der_23611 v h) (by intro d hd; cases hd)))
def cl_24571 : CNF.NClause := [(83,true),(23,true),(4,false),(11,false),(17,true),(5,false)]
theorem der_24571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24571 :=
  CNF.rup_sound cl_24571 [cl_1401,cl_24569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1401 v h) (hints_cons _ _ _ (der_24569 v h) (by intro d hd; cases hd)))
def cl_24572 : CNF.NClause := [(70,true),(17,true),(3,false),(6,false),(14,true),(20,true)]
theorem der_24572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24572 :=
  CNF.rup_sound cl_24572 [cl_541,cl_23602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_541 v h) (hints_cons _ _ _ (der_23602 v h) (by intro d hd; cases hd)))
def cl_24573 : CNF.NClause := [(83,true),(26,false),(4,true),(23,false),(5,false),(17,true)]
theorem der_24573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24573 :=
  CNF.rup_sound cl_24573 [cl_1354,cl_23530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1354 v h) (hints_cons _ _ _ (der_23530 v h) (by intro d hd; cases hd)))
def cl_24574 : CNF.NClause := [(83,true),(17,true),(5,false),(4,true),(23,true),(26,false)]
theorem der_24574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24574 :=
  CNF.rup_sound cl_24574 [cl_1370,cl_23532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1370 v h) (hints_cons _ _ _ (der_23532 v h) (by intro d hd; cases hd)))
def cl_24575 : CNF.NClause := [(83,true),(26,true),(23,false),(11,false),(5,false),(4,true)]
theorem der_24575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24575 :=
  CNF.rup_sound cl_24575 [cl_1386,cl_1378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1386 v h) (hints_cons _ _ _ (inp_1378 v h) (by intro d hd; cases hd)))
def cl_24576 : CNF.NClause := [(76,true),(27,false),(8,true),(10,false),(1,false),(24,false)]
theorem der_24576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24576 :=
  CNF.rup_sound cl_24576 [cl_907,cl_23990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_907 v h) (hints_cons _ _ _ (der_23990 v h) (by intro d hd; cases hd)))
def cl_24577 : CNF.NClause := [(76,true),(8,true),(10,false),(1,false),(24,true),(27,false)]
theorem der_24577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24577 :=
  CNF.rup_sound cl_24577 [cl_923,cl_24314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_923 v h) (hints_cons _ _ _ (der_24314 v h) (by intro d hd; cases hd)))
def cl_24578 : CNF.NClause := [(76,true),(10,false),(1,true),(8,true),(24,false),(27,false)]
theorem der_24578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24578 :=
  CNF.rup_sound cl_24578 [cl_908,cl_900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_908 v h) (hints_cons _ _ _ (inp_900 v h) (by intro d hd; cases hd)))
def cl_24579 : CNF.NClause := [(76,true),(10,false),(1,true),(17,true),(24,true),(27,false)]
theorem der_24579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24579 :=
  CNF.rup_sound cl_24579 [cl_924,cl_24198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_924 v h) (hints_cons _ _ _ (der_24198 v h) (by intro d hd; cases hd)))
def cl_24580 : CNF.NClause := [(76,true),(10,false),(1,true),(8,true),(24,false),(27,true)]
theorem der_24580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24580 :=
  CNF.rup_sound cl_24580 [cl_940,cl_23594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_940 v h) (hints_cons _ _ _ (der_23594 v h) (by intro d hd; cases hd)))
def cl_24581 : CNF.NClause := [(70,true),(20,false),(28,false),(6,false),(3,false),(14,false)]
theorem der_24581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24581 :=
  CNF.rup_sound cl_24581 [cl_521,cl_513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_521 v h) (hints_cons _ _ _ (inp_513 v h) (by intro d hd; cases hd)))
def cl_24582 : CNF.NClause := [(70,true),(28,false),(17,true),(6,false),(3,false),(14,false)]
theorem der_24582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24582 :=
  CNF.rup_sound cl_24582 [cl_537,cl_24581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_537 v h) (hints_cons _ _ _ (der_24581 v h) (by intro d hd; cases hd)))
def cl_24583 : CNF.NClause := [(70,true),(28,true),(6,false),(3,false),(20,false),(17,true)]
theorem der_24583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24583 :=
  CNF.rup_sound cl_24583 [cl_553,cl_557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_553 v h) (hints_cons _ _ _ (inp_557 v h) (by intro d hd; cases hd)))
def cl_24584 : CNF.NClause := [(70,true),(3,false),(28,true),(6,false),(17,true),(20,true)]
theorem der_24584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24584 :=
  CNF.rup_sound cl_24584 [cl_569,cl_23602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_569 v h) (hints_cons _ _ _ (der_23602 v h) (by intro d hd; cases hd)))
def cl_24585 : CNF.NClause := [(70,true),(20,false),(3,false),(14,true),(6,false),(17,true)]
theorem der_24585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24585 :=
  CNF.rup_sound cl_24585 [cl_525,cl_557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_525 v h) (hints_cons _ _ _ (inp_557 v h) (by intro d hd; cases hd)))
def cl_24586 : CNF.NClause := [(84,true),(2,false),(5,false),(28,false),(16,false),(24,false)]
theorem der_24586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24586 :=
  CNF.rup_sound cl_24586 [cl_1413,cl_23616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1413 v h) (hints_cons _ _ _ (der_23616 v h) (by intro d hd; cases hd)))
def cl_24587 : CNF.NClause := [(84,true),(2,false),(5,false),(16,true),(24,false),(28,false)]
theorem der_24587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24587 :=
  CNF.rup_sound cl_24587 [cl_1421,cl_23626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1421 v h) (hints_cons _ _ _ (der_23626 v h) (by intro d hd; cases hd)))
def cl_24588 : CNF.NClause := [(84,true),(2,false),(5,false),(16,false),(24,true),(28,false)]
theorem der_24588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24588 :=
  CNF.rup_sound cl_24588 [cl_1429,cl_24307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1429 v h) (hints_cons _ _ _ (der_24307 v h) (by intro d hd; cases hd)))
def cl_24589 : CNF.NClause := [(84,true),(16,true),(2,false),(5,false),(24,true),(28,false)]
theorem der_24589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24589 :=
  CNF.rup_sound cl_24589 [cl_1437,cl_23626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1437 v h) (hints_cons _ _ _ (der_23626 v h) (by intro d hd; cases hd)))
def cl_24590 : CNF.NClause := [(84,true),(2,false),(5,false),(16,false),(24,false),(28,true)]
theorem der_24590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24590 :=
  CNF.rup_sound cl_24590 [cl_1445,cl_24453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1445 v h) (hints_cons _ _ _ (der_24453 v h) (by intro d hd; cases hd)))
def cl_24591 : CNF.NClause := [(84,true),(13,true),(2,false),(5,false),(16,true),(24,false)]
theorem der_24591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24591 :=
  CNF.rup_sound cl_24591 [cl_1453,cl_24587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1453 v h) (hints_cons _ _ _ (der_24587 v h) (by intro d hd; cases hd)))
def cl_24592 : CNF.NClause := [(84,true),(16,false),(2,false),(13,true),(5,false),(24,true)]
theorem der_24592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24592 :=
  CNF.rup_sound cl_24592 [cl_1461,cl_24588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1461 v h) (hints_cons _ _ _ (der_24588 v h) (by intro d hd; cases hd)))
def cl_24593 : CNF.NClause := [(84,true),(16,true),(2,false),(5,false),(13,true),(24,true)]
theorem der_24593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24593 :=
  CNF.rup_sound cl_24593 [cl_1469,cl_24589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1469 v h) (hints_cons _ _ _ (der_24589 v h) (by intro d hd; cases hd)))
def cl_24594 : CNF.NClause := [(78,true),(27,false),(4,false),(6,false),(22,false),(15,false)]
theorem der_24594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24594 :=
  CNF.rup_sound cl_24594 [cl_1029,cl_1025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1029 v h) (hints_cons _ _ _ (inp_1025 v h) (by intro d hd; cases hd)))
def cl_24595 : CNF.NClause := [(78,true),(27,false),(4,false),(6,false),(22,false),(15,true)]
theorem der_24595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24595 :=
  CNF.rup_sound cl_24595 [cl_1037,cl_24329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1037 v h) (hints_cons _ _ _ (der_24329 v h) (by intro d hd; cases hd)))
def cl_24596 : CNF.NClause := [(78,true),(27,false),(4,false),(6,false),(22,true),(15,false)]
theorem der_24596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24596 :=
  CNF.rup_sound cl_24596 [cl_1045,cl_23632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1045 v h) (hints_cons _ _ _ (der_23632 v h) (by intro d hd; cases hd)))
def cl_24597 : CNF.NClause := [(78,true),(4,false),(6,false),(13,true),(22,true),(27,false)]
theorem der_24597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24597 :=
  CNF.rup_sound cl_24597 [cl_1053,cl_24596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1053 v h) (hints_cons _ _ _ (der_24596 v h) (by intro d hd; cases hd)))
def cl_24598 : CNF.NClause := [(78,true),(4,false),(15,false),(22,false),(6,false),(13,true)]
theorem der_24598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24598 :=
  CNF.rup_sound cl_24598 [cl_1061,cl_24594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1061 v h) (hints_cons _ _ _ (der_24594 v h) (by intro d hd; cases hd)))
def cl_24599 : CNF.NClause := [(78,true),(22,false),(4,false),(6,false),(15,true),(27,true)]
theorem der_24599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24599 :=
  CNF.rup_sound cl_24599 [cl_1069,cl_24331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1069 v h) (hints_cons _ _ _ (der_24331 v h) (by intro d hd; cases hd)))
def cl_24600 : CNF.NClause := [(78,true),(15,false),(4,false),(6,false),(22,true),(27,true)]
theorem der_24600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24600 :=
  CNF.rup_sound cl_24600 [cl_1077,cl_1073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1077 v h) (hints_cons _ _ _ (inp_1073 v h) (by intro d hd; cases hd)))
def cl_24601 : CNF.NClause := [(78,true),(15,true),(4,false),(6,false),(13,true),(27,true)]
theorem der_24601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24601 :=
  CNF.rup_sound cl_24601 [cl_1085,cl_24599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1085 v h) (hints_cons _ _ _ (der_24599 v h) (by intro d hd; cases hd)))
def cl_24602 : CNF.NClause := [(71,true),(20,false),(7,true),(19,false),(13,true),(26,false)]
theorem der_24602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24602 :=
  CNF.rup_sound cl_24602 [cl_584,cl_23466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_584 v h) (hints_cons _ _ _ (der_23466 v h) (by intro d hd; cases hd)))
def cl_24603 : CNF.NClause := [(71,true),(13,true),(1,true),(7,true),(19,false),(26,false)]
theorem der_24603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24603 :=
  CNF.rup_sound cl_24603 [cl_600,cl_24602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_600 v h) (hints_cons _ _ _ (der_24602 v h) (by intro d hd; cases hd)))
def cl_24604 : CNF.NClause := [(71,true),(1,true),(7,true),(20,false),(19,false),(26,true)]
theorem der_24604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24604 :=
  CNF.rup_sound cl_24604 [cl_616,cl_23623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_616 v h) (hints_cons _ _ _ (der_23623 v h) (by intro d hd; cases hd)))
def cl_24605 : CNF.NClause := [(84,true),(2,true),(5,true),(28,false),(16,false),(24,false)]
theorem der_24605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24605 :=
  CNF.rup_sound cl_24605 [cl_1416,cl_24106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1416 v h) (hints_cons _ _ _ (der_24106 v h) (by intro d hd; cases hd)))
def cl_24606 : CNF.NClause := [(84,true),(5,true),(2,true),(13,true),(28,false),(16,false)]
theorem der_24606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24606 :=
  CNF.rup_sound cl_24606 [cl_1432,cl_24605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1432 v h) (hints_cons _ _ _ (der_24605 v h) (by intro d hd; cases hd)))
def cl_24607 : CNF.NClause := [(84,true),(28,true),(5,true),(13,true),(16,false),(24,false)]
theorem der_24607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24607 :=
  CNF.rup_sound cl_24607 [cl_1448,cl_24085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1448 v h) (hints_cons _ _ _ (der_24085 v h) (by intro d hd; cases hd)))
def cl_24608 : CNF.NClause := [(78,true),(22,false),(4,false),(6,true),(27,false),(15,false)]
theorem der_24608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24608 :=
  CNF.rup_sound cl_24608 [cl_1031,cl_24032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1031 v h) (hints_cons _ _ _ (der_24032 v h) (by intro d hd; cases hd)))
def cl_24609 : CNF.NClause := [(78,true),(6,true),(4,false),(15,false),(27,false),(22,true)]
theorem der_24609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24609 :=
  CNF.rup_sound cl_24609 [cl_1047,cl_24034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1047 v h) (hints_cons _ _ _ (der_24034 v h) (by intro d hd; cases hd)))
def cl_24610 : CNF.NClause := [(78,true),(15,false),(4,false),(22,false),(6,true),(27,true)]
theorem der_24610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24610 :=
  CNF.rup_sound cl_24610 [cl_1063,cl_24036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1063 v h) (hints_cons _ _ _ (der_24036 v h) (by intro d hd; cases hd)))
def cl_24611 : CNF.NClause := [(78,true),(15,false),(4,false),(27,true),(6,true),(22,true)]
theorem der_24611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24611 :=
  CNF.rup_sound cl_24611 [cl_1079,cl_24057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1079 v h) (hints_cons _ _ _ (der_24057 v h) (by intro d hd; cases hd)))
def cl_24612 : CNF.NClause := [(71,true),(20,false),(26,false),(7,true),(13,true),(19,true)]
theorem der_24612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24612 :=
  CNF.rup_sound cl_24612 [cl_592,cl_23465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_592 v h) (hints_cons _ _ _ (der_23465 v h) (by intro d hd; cases hd)))
def cl_24613 : CNF.NClause := [(84,true),(2,true),(5,false),(16,false),(24,false),(28,false)]
theorem der_24613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24613 :=
  CNF.rup_sound cl_24613 [cl_1414,cl_1410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1414 v h) (hints_cons _ _ _ (inp_1410 v h) (by intro d hd; cases hd)))
def cl_24614 : CNF.NClause := [(84,true),(13,true),(5,false),(16,true),(24,false),(28,false)]
theorem der_24614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24614 :=
  CNF.rup_sound cl_24614 [cl_1422,cl_24587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1422 v h) (hints_cons _ _ _ (der_24587 v h) (by intro d hd; cases hd)))
def cl_24615 : CNF.NClause := [(84,true),(2,true),(5,false),(16,false),(24,true),(28,false)]
theorem der_24615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24615 :=
  CNF.rup_sound cl_24615 [cl_1430,cl_23615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1430 v h) (hints_cons _ _ _ (der_23615 v h) (by intro d hd; cases hd)))
def cl_24616 : CNF.NClause := [(84,true),(13,true),(5,false),(16,true),(24,true),(28,false)]
theorem der_24616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24616 :=
  CNF.rup_sound cl_24616 [cl_1438,cl_24589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1438 v h) (hints_cons _ _ _ (der_24589 v h) (by intro d hd; cases hd)))
def cl_24617 : CNF.NClause := [(84,true),(2,true),(5,false),(16,false),(24,false),(28,true)]
theorem der_24617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24617 :=
  CNF.rup_sound cl_24617 [cl_1446,cl_23617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1446 v h) (hints_cons _ _ _ (der_23617 v h) (by intro d hd; cases hd)))
def cl_24618 : CNF.NClause := [(84,true),(2,true),(5,false),(16,true),(24,false),(28,true)]
theorem der_24618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24618 :=
  CNF.rup_sound cl_24618 [cl_1454,cl_23618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1454 v h) (hints_cons _ _ _ (der_23618 v h) (by intro d hd; cases hd)))
def cl_24619 : CNF.NClause := [(84,true),(16,false),(2,true),(5,false),(24,true),(28,true)]
theorem der_24619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24619 :=
  CNF.rup_sound cl_24619 [cl_1462,cl_23619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1462 v h) (hints_cons _ _ _ (der_23619 v h) (by intro d hd; cases hd)))
def cl_24620 : CNF.NClause := [(78,true),(27,false),(13,true),(6,false),(22,false),(15,false)]
theorem der_24620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24620 :=
  CNF.rup_sound cl_24620 [cl_1030,cl_24594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1030 v h) (hints_cons _ _ _ (der_24594 v h) (by intro d hd; cases hd)))
def cl_24621 : CNF.NClause := [(78,true),(15,true),(4,true),(6,false),(22,false),(27,false)]
theorem der_24621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24621 :=
  CNF.rup_sound cl_24621 [cl_1038,cl_24349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1038 v h) (hints_cons _ _ _ (der_24349 v h) (by intro d hd; cases hd)))
def cl_24622 : CNF.NClause := [(78,true),(27,false),(4,true),(6,false),(22,true),(15,false)]
theorem der_24622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24622 :=
  CNF.rup_sound cl_24622 [cl_1046,cl_24520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1046 v h) (hints_cons _ _ _ (der_24520 v h) (by intro d hd; cases hd)))
def cl_24623 : CNF.NClause := [(78,true),(15,true),(4,true),(6,false),(22,true),(27,false)]
theorem der_24623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24623 :=
  CNF.rup_sound cl_24623 [cl_1054,cl_24350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1054 v h) (hints_cons _ _ _ (der_24350 v h) (by intro d hd; cases hd)))
def cl_24624 : CNF.NClause := [(78,true),(4,true),(22,false),(15,false),(6,false),(27,true)]
theorem der_24624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24624 :=
  CNF.rup_sound cl_24624 [cl_1062,cl_24259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1062 v h) (hints_cons _ _ _ (der_24259 v h) (by intro d hd; cases hd)))
def cl_24625 : CNF.NClause := [(78,true),(13,true),(15,true),(6,false),(22,false),(27,true)]
theorem der_24625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24625 :=
  CNF.rup_sound cl_24625 [cl_1070,cl_24599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1070 v h) (hints_cons _ _ _ (der_24599 v h) (by intro d hd; cases hd)))
def cl_24626 : CNF.NClause := [(71,true),(13,true),(7,true),(1,false),(19,false),(26,false)]
theorem der_24626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24626 :=
  CNF.rup_sound cl_24626 [cl_599,cl_23466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_599 v h) (hints_cons _ _ _ (der_23466 v h) (by intro d hd; cases hd)))
def cl_24627 : CNF.NClause := [(71,true),(26,false),(7,true),(1,false),(19,true),(13,true)]
theorem der_24627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24627 :=
  CNF.rup_sound cl_24627 [cl_607,cl_23465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_607 v h) (hints_cons _ _ _ (der_23465 v h) (by intro d hd; cases hd)))
def cl_24628 : CNF.NClause := [(71,true),(20,false),(7,true),(1,false),(19,false),(13,true)]
theorem der_24628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24628 :=
  CNF.rup_sound cl_24628 [cl_615,cl_23466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_615 v h) (hints_cons _ _ _ (der_23466 v h) (by intro d hd; cases hd)))
def cl_24629 : CNF.NClause := [(71,true),(13,true),(1,false),(7,false),(19,false),(26,false)]
theorem der_24629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24629 :=
  CNF.rup_sound cl_24629 [cl_597,cl_23466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_597 v h) (hints_cons _ _ _ (der_23466 v h) (by intro d hd; cases hd)))
def cl_24630 : CNF.NClause := [(71,true),(26,false),(13,true),(7,false),(19,true),(1,false)]
theorem der_24630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24630 :=
  CNF.rup_sound cl_24630 [cl_605,cl_23465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_605 v h) (hints_cons _ _ _ (der_23465 v h) (by intro d hd; cases hd)))
def cl_24631 : CNF.NClause := [(71,true),(13,true),(1,false),(7,false),(19,false),(20,false)]
theorem der_24631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24631 :=
  CNF.rup_sound cl_24631 [cl_613,cl_23466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_613 v h) (hints_cons _ _ _ (der_23466 v h) (by intro d hd; cases hd)))
def cl_24632 : CNF.NClause := [(71,true),(13,true),(1,false),(7,false),(19,true),(20,false)]
theorem der_24632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24632 :=
  CNF.rup_sound cl_24632 [cl_621,cl_23465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_621 v h) (hints_cons _ _ _ (der_23465 v h) (by intro d hd; cases hd)))
def cl_24633 : CNF.NClause := [(71,true),(13,true),(1,false),(19,false),(20,true),(26,true)]
theorem der_24633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24633 :=
  CNF.rup_sound cl_24633 [cl_629,cl_24164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_629 v h) (hints_cons _ _ _ (der_24164 v h) (by intro d hd; cases hd)))
def cl_24634 : CNF.NClause := [(71,true),(13,true),(7,false),(19,true),(20,true),(1,false)]
theorem der_24634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24634 :=
  CNF.rup_sound cl_24634 [cl_637,cl_24630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_637 v h) (hints_cons _ _ _ (der_24630 v h) (by intro d hd; cases hd)))
def cl_24635 : CNF.NClause := [(75,true),(9,true),(10,false),(16,false),(22,false),(26,false)]
theorem der_24635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24635 :=
  CNF.rup_sound cl_24635 [cl_835,cl_24437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_835 v h) (hints_cons _ _ _ (der_24437 v h) (by intro d hd; cases hd)))
def cl_24636 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(26,false)]
theorem der_24636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24636 :=
  CNF.rup_sound cl_24636 [cl_851,cl_24635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_851 v h) (hints_cons _ _ _ (der_24635 v h) (by intro d hd; cases hd)))
def cl_24637 : CNF.NClause := [(75,true),(26,true),(3,false),(10,false),(16,false),(22,true)]
theorem der_24637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24637 :=
  CNF.rup_sound cl_24637 [cl_883,cl_24273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_883 v h) (hints_cons _ _ _ (der_24273 v h) (by intro d hd; cases hd)))
def cl_24638 : CNF.NClause := [(75,true),(26,true),(3,false),(16,false),(22,true),(9,true)]
theorem der_24638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24638 :=
  CNF.rup_sound cl_24638 [cl_887,cl_24637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_887 v h) (hints_cons _ _ _ (der_24637 v h) (by intro d hd; cases hd)))
def cl_24639 : CNF.NClause := [(75,true),(3,false),(22,true),(10,false),(16,true),(26,true)]
theorem der_24639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24639 :=
  CNF.rup_sound cl_24639 [cl_891,cl_23559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_891 v h) (hints_cons _ _ _ (der_23559 v h) (by intro d hd; cases hd)))
def cl_24640 : CNF.NClause := [(69,true),(2,false),(11,false),(18,false),(20,false),(27,false)]
theorem der_24640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24640 :=
  CNF.rup_sound cl_24640 [cl_451,cl_449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_451 v h) (hints_cons _ _ _ (inp_449 v h) (by intro d hd; cases hd)))
def cl_24641 : CNF.NClause := [(69,true),(9,true),(2,false),(18,false),(20,false),(27,false)]
theorem der_24641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24641 :=
  CNF.rup_sound cl_24641 [cl_455,cl_24640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_455 v h) (hints_cons _ _ _ (der_24640 v h) (by intro d hd; cases hd)))
def cl_24642 : CNF.NClause := [(69,true),(9,true),(2,false),(11,false),(20,false),(27,false)]
theorem der_24642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24642 :=
  CNF.rup_sound cl_24642 [cl_459,cl_24640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_459 v h) (hints_cons _ _ _ (der_24640 v h) (by intro d hd; cases hd)))
def cl_24643 : CNF.NClause := [(69,true),(2,false),(11,true),(18,true),(20,false),(27,false)]
theorem der_24643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24643 :=
  CNF.rup_sound cl_24643 [cl_463,cl_24372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_463 v h) (hints_cons _ _ _ (der_24372 v h) (by intro d hd; cases hd)))
def cl_24644 : CNF.NClause := [(69,true),(2,false),(18,false),(11,false),(20,true),(27,false)]
theorem der_24644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24644 :=
  CNF.rup_sound cl_24644 [cl_467,cl_24175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_467 v h) (hints_cons _ _ _ (der_24175 v h) (by intro d hd; cases hd)))
def cl_24645 : CNF.NClause := [(69,true),(11,true),(2,false),(9,true),(18,false),(27,false)]
theorem der_24645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24645 :=
  CNF.rup_sound cl_24645 [cl_471,cl_24641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_471 v h) (hints_cons _ _ _ (der_24641 v h) (by intro d hd; cases hd)))
def cl_24646 : CNF.NClause := [(69,true),(9,true),(11,false),(18,true),(20,true),(27,false)]
theorem der_24646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24646 :=
  CNF.rup_sound cl_24646 [cl_475,cl_23586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_475 v h) (hints_cons _ _ _ (der_23586 v h) (by intro d hd; cases hd)))
def cl_24647 : CNF.NClause := [(69,true),(11,true),(2,false),(9,true),(20,true),(27,false)]
theorem der_24647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24647 :=
  CNF.rup_sound cl_24647 [cl_479,cl_24645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_479 v h) (hints_cons _ _ _ (der_24645 v h) (by intro d hd; cases hd)))
def cl_24648 : CNF.NClause := [(69,true),(9,true),(11,false),(18,false),(20,false),(27,true)]
theorem der_24648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24648 :=
  CNF.rup_sound cl_24648 [cl_483,cl_24260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_483 v h) (hints_cons _ _ _ (der_24260 v h) (by intro d hd; cases hd)))
def cl_24649 : CNF.NClause := [(69,true),(9,true),(11,true),(18,false),(20,false),(27,true)]
theorem der_24649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24649 :=
  CNF.rup_sound cl_24649 [cl_487,cl_24389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_487 v h) (hints_cons _ _ _ (der_24389 v h) (by intro d hd; cases hd)))
def cl_24650 : CNF.NClause := [(69,true),(9,true),(2,false),(11,false),(18,true),(20,false)]
theorem der_24650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24650 :=
  CNF.rup_sound cl_24650 [cl_491,cl_24642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_491 v h) (hints_cons _ _ _ (der_24642 v h) (by intro d hd; cases hd)))
def cl_24651 : CNF.NClause := [(69,true),(2,false),(11,true),(18,true),(20,false),(27,true)]
theorem der_24651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24651 :=
  CNF.rup_sound cl_24651 [cl_495,cl_24376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_495 v h) (hints_cons _ _ _ (der_24376 v h) (by intro d hd; cases hd)))
def cl_24652 : CNF.NClause := [(69,true),(9,true),(11,false),(18,false),(20,true),(27,true)]
theorem der_24652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24652 :=
  CNF.rup_sound cl_24652 [cl_499,cl_24186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_499 v h) (hints_cons _ _ _ (der_24186 v h) (by intro d hd; cases hd)))
def cl_24653 : CNF.NClause := [(69,true),(11,true),(2,false),(9,true),(18,false),(20,true)]
theorem der_24653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24653 :=
  CNF.rup_sound cl_24653 [cl_503,cl_24645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_503 v h) (hints_cons _ _ _ (der_24645 v h) (by intro d hd; cases hd)))
def cl_24654 : CNF.NClause := [(69,true),(2,false),(11,false),(18,true),(20,true),(27,true)]
theorem der_24654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24654 :=
  CNF.rup_sound cl_24654 [cl_507,cl_23585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_507 v h) (hints_cons _ _ _ (der_23585 v h) (by intro d hd; cases hd)))
def cl_24655 : CNF.NClause := [(81,true),(28,false),(9,true),(15,false),(23,true),(12,true)]
theorem der_24655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24655 :=
  CNF.rup_sound cl_24655 [cl_1239,cl_24253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1239 v h) (hints_cons _ _ _ (der_24253 v h) (by intro d hd; cases hd)))
def cl_24656 : CNF.NClause := [(81,true),(12,true),(1,false),(28,true),(15,false),(9,true)]
theorem der_24656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24656 :=
  CNF.rup_sound cl_24656 [cl_1271,cl_1255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1271 v h) (hints_cons _ _ _ (inp_1255 v h) (by intro d hd; cases hd)))
def cl_24657 : CNF.NClause := [(81,true),(15,true),(12,false),(9,true),(23,true),(1,false)]
theorem der_24657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24657 :=
  CNF.rup_sound cl_24657 [cl_1275,cl_23569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1275 v h) (hints_cons _ _ _ (der_23569 v h) (by intro d hd; cases hd)))
def cl_24658 : CNF.NClause := [(81,true),(12,true),(9,true),(15,false),(1,false),(23,false)]
theorem der_24658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24658 :=
  CNF.rup_sound cl_24658 [cl_1223,cl_1255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1223 v h) (hints_cons _ _ _ (inp_1255 v h) (by intro d hd; cases hd)))
def cl_24659 : CNF.NClause := [(81,true),(12,false),(1,false),(23,false),(9,true),(15,false)]
theorem der_24659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24659 :=
  CNF.rup_sound cl_24659 [cl_1219,cl_23553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1219 v h) (hints_cons _ _ _ (der_23553 v h) (by intro d hd; cases hd)))
def cl_24660 : CNF.NClause := [(69,true),(9,true),(18,false),(2,true),(11,false),(20,false)]
theorem der_24660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24660 :=
  CNF.rup_sound cl_24660 [cl_452,cl_24260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_452 v h) (hints_cons _ _ _ (der_24260 v h) (by intro d hd; cases hd)))
def cl_24661 : CNF.NClause := [(75,true),(9,true),(10,false),(3,false),(22,false),(26,false)]
theorem der_24661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24661 :=
  CNF.rup_sound cl_24661 [cl_843,cl_24635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_843 v h) (hints_cons _ _ _ (der_24635 v h) (by intro d hd; cases hd)))
def cl_24662 : CNF.NClause := [(69,true),(18,true),(2,true),(11,false),(20,false),(27,false)]
theorem der_24662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24662 :=
  CNF.rup_sound cl_24662 [cl_460,cl_23579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_460 v h) (hints_cons _ _ _ (der_23579 v h) (by intro d hd; cases hd)))
def cl_24663 : CNF.NClause := [(75,true),(16,true),(10,false),(22,true),(3,false),(26,false)]
theorem der_24663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24663 :=
  CNF.rup_sound cl_24663 [cl_859,cl_24485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_859 v h) (hints_cons _ _ _ (der_24485 v h) (by intro d hd; cases hd)))
def cl_24664 : CNF.NClause := [(85,true),(27,false),(12,true),(5,true),(3,true),(21,false)]
theorem der_24664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24664 :=
  CNF.rup_sound cl_24664 [cl_1488,cl_24285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1488 v h) (hints_cons _ _ _ (der_24285 v h) (by intro d hd; cases hd)))
def cl_24665 : CNF.NClause := [(73,true),(18,true),(4,false),(10,false),(28,false),(7,true)]
theorem der_24665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24665 :=
  CNF.rup_sound cl_24665 [cl_715,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_715 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_24666 : CNF.NClause := [(85,true),(12,false),(3,false),(5,false),(19,false),(21,false)]
theorem der_24666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24666 :=
  CNF.rup_sound cl_24666 [cl_1473,cl_1505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1473 v h) (hints_cons _ _ _ (inp_1505 v h) (by intro d hd; cases hd)))
def cl_24667 : CNF.NClause := [(85,true),(12,true),(3,false),(27,false),(5,false),(19,false)]
theorem der_24667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24667 :=
  CNF.rup_sound cl_24667 [cl_1477,cl_1493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1477 v h) (hints_cons _ _ _ (inp_1493 v h) (by intro d hd; cases hd)))
def cl_24668 : CNF.NClause := [(85,true),(12,true),(27,true),(19,false),(5,false),(3,false)]
theorem der_24668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24668 :=
  CNF.rup_sound cl_24668 [cl_1509,cl_23601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1509 v h) (hints_cons _ _ _ (der_23601 v h) (by intro d hd; cases hd)))
def cl_24669 : CNF.NClause := [(79,true),(26,false),(21,false),(15,false),(8,false),(14,true)]
theorem der_24669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24669 :=
  CNF.rup_sound cl_24669 [cl_1093,cl_23501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1093 v h) (hints_cons _ _ _ (der_23501 v h) (by intro d hd; cases hd)))
def cl_24670 : CNF.NClause := [(79,true),(8,false),(14,true),(2,false),(15,false),(21,false)]
theorem der_24670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24670 :=
  CNF.rup_sound cl_24670 [cl_1125,cl_24669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1125 v h) (hints_cons _ _ _ (der_24669 v h) (by intro d hd; cases hd)))
def cl_24671 : CNF.NClause := [(79,true),(14,false),(8,false),(15,false),(21,false),(26,false)]
theorem der_24671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24671 :=
  CNF.rup_sound cl_24671 [cl_1089,cl_1090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1089 v h) (hints_cons _ _ _ (inp_1090 v h) (by intro d hd; cases hd)))
def cl_24672 : CNF.NClause := [(85,true),(3,false),(12,false),(27,false),(19,true),(21,false)]
theorem der_24672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24672 :=
  CNF.rup_sound cl_24672 [cl_1481,cl_24096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1481 v h) (hints_cons _ _ _ (der_24096 v h) (by intro d hd; cases hd)))
def cl_24673 : CNF.NClause := [(85,true),(3,false),(27,true),(5,false),(12,false),(21,false)]
theorem der_24673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24673 :=
  CNF.rup_sound cl_24673 [cl_1513,cl_1505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1513 v h) (hints_cons _ _ _ (inp_1505 v h) (by intro d hd; cases hd)))
def cl_24674 : CNF.NClause := [(73,true),(10,false),(4,false),(7,true),(18,false),(21,false)]
theorem der_24674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24674 :=
  CNF.rup_sound cl_24674 [cl_739,cl_23499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_739 v h) (hints_cons _ _ _ (der_23499 v h) (by intro d hd; cases hd)))
def cl_24675 : CNF.NClause := [(73,true),(4,true),(28,true),(10,false),(7,true),(21,false)]
theorem der_24675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24675 :=
  CNF.rup_sound cl_24675 [cl_740,cl_24166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_740 v h) (hints_cons _ _ _ (der_24166 v h) (by intro d hd; cases hd)))
def cl_24676 : CNF.NClause := [(73,true),(10,false),(4,false),(18,true),(7,false),(28,false)]
theorem der_24676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24676 :=
  CNF.rup_sound cl_24676 [cl_713,cl_16146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_713 v h) (hints_cons _ _ _ (der_16146 v h) (by intro d hd; cases hd)))
def cl_24677 : CNF.NClause := [(31,false),(92,true),(90,false),(87,true),(88,false),(91,false)]
theorem der_24677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24677 :=
  CNF.rup_sound cl_24677 [cl_15458,cl_15462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15458 v h) (hints_cons _ _ _ (der_15462 v h) (by intro d hd; cases hd)))
def chunk004 : List CNF.NClause := [cl_24178,cl_24179,cl_24180,cl_24181,cl_24182,cl_24183,cl_24184,cl_24185,cl_24186,cl_24187,cl_24188,cl_24189,cl_24190,cl_24191,cl_24192,cl_24193,cl_24194,cl_24195,cl_24196,cl_24197,cl_24198,cl_24199,cl_24200,cl_24201,cl_24202,cl_24203,cl_24204,cl_24205,cl_24206,cl_24207,cl_24208,cl_24209,cl_24210,cl_24211,cl_24212,cl_24213,cl_24214,cl_24215,cl_24216,cl_24217,cl_24218,cl_24219,cl_24220,cl_24221,cl_24222,cl_24223,cl_24224,cl_24225,cl_24226,cl_24227,cl_24228,cl_24229,cl_24230,cl_24231,cl_24232,cl_24233,cl_24234,cl_24235,cl_24236,cl_24237,cl_24238,cl_24239,cl_24240,cl_24241,cl_24242,cl_24243,cl_24244,cl_24245,cl_24246,cl_24247,cl_24248,cl_24249,cl_24250,cl_24251,cl_24252,cl_24253,cl_24254,cl_24255,cl_24256,cl_24257,cl_24258,cl_24259,cl_24260,cl_24261,cl_24262,cl_24263,cl_24264,cl_24265,cl_24266,cl_24267,cl_24268,cl_24269,cl_24270,cl_24271,cl_24272,cl_24273,cl_24274,cl_24275,cl_24276,cl_24277,cl_24278,cl_24279,cl_24280,cl_24281,cl_24282,cl_24283,cl_24284,cl_24285,cl_24286,cl_24287,cl_24288,cl_24289,cl_24290,cl_24291,cl_24292,cl_24293,cl_24294,cl_24295,cl_24296,cl_24297,cl_24298,cl_24299,cl_24300,cl_24301,cl_24302,cl_24303,cl_24304,cl_24305,cl_24306,cl_24307,cl_24308,cl_24309,cl_24310,cl_24311,cl_24312,cl_24313,cl_24314,cl_24315,cl_24316,cl_24317,cl_24318,cl_24319,cl_24320,cl_24321,cl_24322,cl_24323,cl_24324,cl_24325,cl_24326,cl_24327,cl_24328,cl_24329,cl_24330,cl_24331,cl_24332,cl_24333,cl_24334,cl_24335,cl_24336,cl_24337,cl_24338,cl_24339,cl_24340,cl_24341,cl_24342,cl_24343,cl_24344,cl_24345,cl_24346,cl_24347,cl_24348,cl_24349,cl_24350,cl_24351,cl_24352,cl_24353,cl_24354,cl_24355,cl_24356,cl_24357,cl_24358,cl_24359,cl_24360,cl_24361,cl_24362,cl_24363,cl_24364,cl_24365,cl_24366,cl_24367,cl_24368,cl_24369,cl_24370,cl_24371,cl_24372,cl_24373,cl_24374,cl_24375,cl_24376,cl_24377,cl_24378,cl_24379,cl_24380,cl_24381,cl_24382,cl_24383,cl_24384,cl_24385,cl_24386,cl_24387,cl_24388,cl_24389,cl_24390,cl_24391,cl_24392,cl_24393,cl_24394,cl_24395,cl_24396,cl_24397,cl_24398,cl_24399,cl_24400,cl_24401,cl_24402,cl_24403,cl_24404,cl_24405,cl_24406,cl_24407,cl_24408,cl_24409,cl_24410,cl_24411,cl_24412,cl_24413,cl_24414,cl_24415,cl_24416,cl_24417,cl_24418,cl_24419,cl_24420,cl_24421,cl_24422,cl_24423,cl_24424,cl_24425,cl_24426,cl_24427,cl_24428,cl_24429,cl_24430,cl_24431,cl_24432,cl_24433,cl_24434,cl_24435,cl_24436,cl_24437,cl_24438,cl_24439,cl_24440,cl_24441,cl_24442,cl_24443,cl_24444,cl_24445,cl_24446,cl_24447,cl_24448,cl_24449,cl_24450,cl_24451,cl_24452,cl_24453,cl_24454,cl_24455,cl_24456,cl_24457,cl_24458,cl_24459,cl_24460,cl_24461,cl_24462,cl_24463,cl_24464,cl_24465,cl_24466,cl_24467,cl_24468,cl_24469,cl_24470,cl_24471,cl_24472,cl_24473,cl_24474,cl_24475,cl_24476,cl_24477,cl_24478,cl_24479,cl_24480,cl_24481,cl_24482,cl_24483,cl_24484,cl_24485,cl_24486,cl_24487,cl_24488,cl_24489,cl_24490,cl_24491,cl_24492,cl_24493,cl_24494,cl_24495,cl_24496,cl_24497,cl_24498,cl_24499,cl_24500,cl_24501,cl_24502,cl_24503,cl_24504,cl_24505,cl_24506,cl_24507,cl_24508,cl_24509,cl_24510,cl_24511,cl_24512,cl_24513,cl_24514,cl_24515,cl_24516,cl_24517,cl_24518,cl_24519,cl_24520,cl_24521,cl_24522,cl_24523,cl_24524,cl_24525,cl_24526,cl_24527,cl_24528,cl_24529,cl_24530,cl_24531,cl_24532,cl_24533,cl_24534,cl_24535,cl_24536,cl_24537,cl_24538,cl_24539,cl_24540,cl_24541,cl_24542,cl_24543,cl_24544,cl_24545,cl_24546,cl_24547,cl_24548,cl_24549,cl_24550,cl_24551,cl_24552,cl_24553,cl_24554,cl_24555,cl_24556,cl_24557,cl_24558,cl_24559,cl_24560,cl_24561,cl_24562,cl_24563,cl_24564,cl_24565,cl_24566,cl_24567,cl_24568,cl_24569,cl_24570,cl_24571,cl_24572,cl_24573,cl_24574,cl_24575,cl_24576,cl_24577,cl_24578,cl_24579,cl_24580,cl_24581,cl_24582,cl_24583,cl_24584,cl_24585,cl_24586,cl_24587,cl_24588,cl_24589,cl_24590,cl_24591,cl_24592,cl_24593,cl_24594,cl_24595,cl_24596,cl_24597,cl_24598,cl_24599,cl_24600,cl_24601,cl_24602,cl_24603,cl_24604,cl_24605,cl_24606,cl_24607,cl_24608,cl_24609,cl_24610,cl_24611,cl_24612,cl_24613,cl_24614,cl_24615,cl_24616,cl_24617,cl_24618,cl_24619,cl_24620,cl_24621,cl_24622,cl_24623,cl_24624,cl_24625,cl_24626,cl_24627,cl_24628,cl_24629,cl_24630,cl_24631,cl_24632,cl_24633,cl_24634,cl_24635,cl_24636,cl_24637,cl_24638,cl_24639,cl_24640,cl_24641,cl_24642,cl_24643,cl_24644,cl_24645,cl_24646,cl_24647,cl_24648,cl_24649,cl_24650,cl_24651,cl_24652,cl_24653,cl_24654,cl_24655,cl_24656,cl_24657,cl_24658,cl_24659,cl_24660,cl_24661,cl_24662,cl_24663,cl_24664,cl_24665,cl_24666,cl_24667,cl_24668,cl_24669,cl_24670,cl_24671,cl_24672,cl_24673,cl_24674,cl_24675,cl_24676,cl_24677]
theorem chunk_sound004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk004, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_24178 v h) (hints_cons _ _ _ (der_24179 v h) (hints_cons _ _ _ (der_24180 v h) (hints_cons _ _ _ (der_24181 v h) (hints_cons _ _ _ (der_24182 v h) (hints_cons _ _ _ (der_24183 v h) (hints_cons _ _ _ (der_24184 v h) (hints_cons _ _ _ (der_24185 v h) (hints_cons _ _ _ (der_24186 v h) (hints_cons _ _ _ (der_24187 v h) (hints_cons _ _ _ (der_24188 v h) (hints_cons _ _ _ (der_24189 v h) (hints_cons _ _ _ (der_24190 v h) (hints_cons _ _ _ (der_24191 v h) (hints_cons _ _ _ (der_24192 v h) (hints_cons _ _ _ (der_24193 v h) (hints_cons _ _ _ (der_24194 v h) (hints_cons _ _ _ (der_24195 v h) (hints_cons _ _ _ (der_24196 v h) (hints_cons _ _ _ (der_24197 v h) (hints_cons _ _ _ (der_24198 v h) (hints_cons _ _ _ (der_24199 v h) (hints_cons _ _ _ (der_24200 v h) (hints_cons _ _ _ (der_24201 v h) (hints_cons _ _ _ (der_24202 v h) (hints_cons _ _ _ (der_24203 v h) (hints_cons _ _ _ (der_24204 v h) (hints_cons _ _ _ (der_24205 v h) (hints_cons _ _ _ (der_24206 v h) (hints_cons _ _ _ (der_24207 v h) (hints_cons _ _ _ (der_24208 v h) (hints_cons _ _ _ (der_24209 v h) (hints_cons _ _ _ (der_24210 v h) (hints_cons _ _ _ (der_24211 v h) (hints_cons _ _ _ (der_24212 v h) (hints_cons _ _ _ (der_24213 v h) (hints_cons _ _ _ (der_24214 v h) (hints_cons _ _ _ (der_24215 v h) (hints_cons _ _ _ (der_24216 v h) (hints_cons _ _ _ (der_24217 v h) (hints_cons _ _ _ (der_24218 v h) (hints_cons _ _ _ (der_24219 v h) (hints_cons _ _ _ (der_24220 v h) (hints_cons _ _ _ (der_24221 v h) (hints_cons _ _ _ (der_24222 v h) (hints_cons _ _ _ (der_24223 v h) (hints_cons _ _ _ (der_24224 v h) (hints_cons _ _ _ (der_24225 v h) (hints_cons _ _ _ (der_24226 v h) (hints_cons _ _ _ (der_24227 v h) (hints_cons _ _ _ (der_24228 v h) (hints_cons _ _ _ (der_24229 v h) (hints_cons _ _ _ (der_24230 v h) (hints_cons _ _ _ (der_24231 v h) (hints_cons _ _ _ (der_24232 v h) (hints_cons _ _ _ (der_24233 v h) (hints_cons _ _ _ (der_24234 v h) (hints_cons _ _ _ (der_24235 v h) (hints_cons _ _ _ (der_24236 v h) (hints_cons _ _ _ (der_24237 v h) (hints_cons _ _ _ (der_24238 v h) (hints_cons _ _ _ (der_24239 v h) (hints_cons _ _ _ (der_24240 v h) (hints_cons _ _ _ (der_24241 v h) (hints_cons _ _ _ (der_24242 v h) (hints_cons _ _ _ (der_24243 v h) (hints_cons _ _ _ (der_24244 v h) (hints_cons _ _ _ (der_24245 v h) (hints_cons _ _ _ (der_24246 v h) (hints_cons _ _ _ (der_24247 v h) (hints_cons _ _ _ (der_24248 v h) (hints_cons _ _ _ (der_24249 v h) (hints_cons _ _ _ (der_24250 v h) (hints_cons _ _ _ (der_24251 v h) (hints_cons _ _ _ (der_24252 v h) (hints_cons _ _ _ (der_24253 v h) (hints_cons _ _ _ (der_24254 v h) (hints_cons _ _ _ (der_24255 v h) (hints_cons _ _ _ (der_24256 v h) (hints_cons _ _ _ (der_24257 v h) (hints_cons _ _ _ (der_24258 v h) (hints_cons _ _ _ (der_24259 v h) (hints_cons _ _ _ (der_24260 v h) (hints_cons _ _ _ (der_24261 v h) (hints_cons _ _ _ (der_24262 v h) (hints_cons _ _ _ (der_24263 v h) (hints_cons _ _ _ (der_24264 v h) (hints_cons _ _ _ (der_24265 v h) (hints_cons _ _ _ (der_24266 v h) (hints_cons _ _ _ (der_24267 v h) (hints_cons _ _ _ (der_24268 v h) (hints_cons _ _ _ (der_24269 v h) (hints_cons _ _ _ (der_24270 v h) (hints_cons _ _ _ (der_24271 v h) (hints_cons _ _ _ (der_24272 v h) (hints_cons _ _ _ (der_24273 v h) (hints_cons _ _ _ (der_24274 v h) (hints_cons _ _ _ (der_24275 v h) (hints_cons _ _ _ (der_24276 v h) (hints_cons _ _ _ (der_24277 v h) (hints_cons _ _ _ (der_24278 v h) (hints_cons _ _ _ (der_24279 v h) (hints_cons _ _ _ (der_24280 v h) (hints_cons _ _ _ (der_24281 v h) (hints_cons _ _ _ (der_24282 v h) (hints_cons _ _ _ (der_24283 v h) (hints_cons _ _ _ (der_24284 v h) (hints_cons _ _ _ (der_24285 v h) (hints_cons _ _ _ (der_24286 v h) (hints_cons _ _ _ (der_24287 v h) (hints_cons _ _ _ (der_24288 v h) (hints_cons _ _ _ (der_24289 v h) (hints_cons _ _ _ (der_24290 v h) (hints_cons _ _ _ (der_24291 v h) (hints_cons _ _ _ (der_24292 v h) (hints_cons _ _ _ (der_24293 v h) (hints_cons _ _ _ (der_24294 v h) (hints_cons _ _ _ (der_24295 v h) (hints_cons _ _ _ (der_24296 v h) (hints_cons _ _ _ (der_24297 v h) (hints_cons _ _ _ (der_24298 v h) (hints_cons _ _ _ (der_24299 v h) (hints_cons _ _ _ (der_24300 v h) (hints_cons _ _ _ (der_24301 v h) (hints_cons _ _ _ (der_24302 v h) (hints_cons _ _ _ (der_24303 v h) (hints_cons _ _ _ (der_24304 v h) (hints_cons _ _ _ (der_24305 v h) (hints_cons _ _ _ (der_24306 v h) (hints_cons _ _ _ (der_24307 v h) (hints_cons _ _ _ (der_24308 v h) (hints_cons _ _ _ (der_24309 v h) (hints_cons _ _ _ (der_24310 v h) (hints_cons _ _ _ (der_24311 v h) (hints_cons _ _ _ (der_24312 v h) (hints_cons _ _ _ (der_24313 v h) (hints_cons _ _ _ (der_24314 v h) (hints_cons _ _ _ (der_24315 v h) (hints_cons _ _ _ (der_24316 v h) (hints_cons _ _ _ (der_24317 v h) (hints_cons _ _ _ (der_24318 v h) (hints_cons _ _ _ (der_24319 v h) (hints_cons _ _ _ (der_24320 v h) (hints_cons _ _ _ (der_24321 v h) (hints_cons _ _ _ (der_24322 v h) (hints_cons _ _ _ (der_24323 v h) (hints_cons _ _ _ (der_24324 v h) (hints_cons _ _ _ (der_24325 v h) (hints_cons _ _ _ (der_24326 v h) (hints_cons _ _ _ (der_24327 v h) (hints_cons _ _ _ (der_24328 v h) (hints_cons _ _ _ (der_24329 v h) (hints_cons _ _ _ (der_24330 v h) (hints_cons _ _ _ (der_24331 v h) (hints_cons _ _ _ (der_24332 v h) (hints_cons _ _ _ (der_24333 v h) (hints_cons _ _ _ (der_24334 v h) (hints_cons _ _ _ (der_24335 v h) (hints_cons _ _ _ (der_24336 v h) (hints_cons _ _ _ (der_24337 v h) (hints_cons _ _ _ (der_24338 v h) (hints_cons _ _ _ (der_24339 v h) (hints_cons _ _ _ (der_24340 v h) (hints_cons _ _ _ (der_24341 v h) (hints_cons _ _ _ (der_24342 v h) (hints_cons _ _ _ (der_24343 v h) (hints_cons _ _ _ (der_24344 v h) (hints_cons _ _ _ (der_24345 v h) (hints_cons _ _ _ (der_24346 v h) (hints_cons _ _ _ (der_24347 v h) (hints_cons _ _ _ (der_24348 v h) (hints_cons _ _ _ (der_24349 v h) (hints_cons _ _ _ (der_24350 v h) (hints_cons _ _ _ (der_24351 v h) (hints_cons _ _ _ (der_24352 v h) (hints_cons _ _ _ (der_24353 v h) (hints_cons _ _ _ (der_24354 v h) (hints_cons _ _ _ (der_24355 v h) (hints_cons _ _ _ (der_24356 v h) (hints_cons _ _ _ (der_24357 v h) (hints_cons _ _ _ (der_24358 v h) (hints_cons _ _ _ (der_24359 v h) (hints_cons _ _ _ (der_24360 v h) (hints_cons _ _ _ (der_24361 v h) (hints_cons _ _ _ (der_24362 v h) (hints_cons _ _ _ (der_24363 v h) (hints_cons _ _ _ (der_24364 v h) (hints_cons _ _ _ (der_24365 v h) (hints_cons _ _ _ (der_24366 v h) (hints_cons _ _ _ (der_24367 v h) (hints_cons _ _ _ (der_24368 v h) (hints_cons _ _ _ (der_24369 v h) (hints_cons _ _ _ (der_24370 v h) (hints_cons _ _ _ (der_24371 v h) (hints_cons _ _ _ (der_24372 v h) (hints_cons _ _ _ (der_24373 v h) (hints_cons _ _ _ (der_24374 v h) (hints_cons _ _ _ (der_24375 v h) (hints_cons _ _ _ (der_24376 v h) (hints_cons _ _ _ (der_24377 v h) (hints_cons _ _ _ (der_24378 v h) (hints_cons _ _ _ (der_24379 v h) (hints_cons _ _ _ (der_24380 v h) (hints_cons _ _ _ (der_24381 v h) (hints_cons _ _ _ (der_24382 v h) (hints_cons _ _ _ (der_24383 v h) (hints_cons _ _ _ (der_24384 v h) (hints_cons _ _ _ (der_24385 v h) (hints_cons _ _ _ (der_24386 v h) (hints_cons _ _ _ (der_24387 v h) (hints_cons _ _ _ (der_24388 v h) (hints_cons _ _ _ (der_24389 v h) (hints_cons _ _ _ (der_24390 v h) (hints_cons _ _ _ (der_24391 v h) (hints_cons _ _ _ (der_24392 v h) (hints_cons _ _ _ (der_24393 v h) (hints_cons _ _ _ (der_24394 v h) (hints_cons _ _ _ (der_24395 v h) (hints_cons _ _ _ (der_24396 v h) (hints_cons _ _ _ (der_24397 v h) (hints_cons _ _ _ (der_24398 v h) (hints_cons _ _ _ (der_24399 v h) (hints_cons _ _ _ (der_24400 v h) (hints_cons _ _ _ (der_24401 v h) (hints_cons _ _ _ (der_24402 v h) (hints_cons _ _ _ (der_24403 v h) (hints_cons _ _ _ (der_24404 v h) (hints_cons _ _ _ (der_24405 v h) (hints_cons _ _ _ (der_24406 v h) (hints_cons _ _ _ (der_24407 v h) (hints_cons _ _ _ (der_24408 v h) (hints_cons _ _ _ (der_24409 v h) (hints_cons _ _ _ (der_24410 v h) (hints_cons _ _ _ (der_24411 v h) (hints_cons _ _ _ (der_24412 v h) (hints_cons _ _ _ (der_24413 v h) (hints_cons _ _ _ (der_24414 v h) (hints_cons _ _ _ (der_24415 v h) (hints_cons _ _ _ (der_24416 v h) (hints_cons _ _ _ (der_24417 v h) (hints_cons _ _ _ (der_24418 v h) (hints_cons _ _ _ (der_24419 v h) (hints_cons _ _ _ (der_24420 v h) (hints_cons _ _ _ (der_24421 v h) (hints_cons _ _ _ (der_24422 v h) (hints_cons _ _ _ (der_24423 v h) (hints_cons _ _ _ (der_24424 v h) (hints_cons _ _ _ (der_24425 v h) (hints_cons _ _ _ (der_24426 v h) (hints_cons _ _ _ (der_24427 v h) (hints_cons _ _ _ (der_24428 v h) (hints_cons _ _ _ (der_24429 v h) (hints_cons _ _ _ (der_24430 v h) (hints_cons _ _ _ (der_24431 v h) (hints_cons _ _ _ (der_24432 v h) (hints_cons _ _ _ (der_24433 v h) (hints_cons _ _ _ (der_24434 v h) (hints_cons _ _ _ (der_24435 v h) (hints_cons _ _ _ (der_24436 v h) (hints_cons _ _ _ (der_24437 v h) (hints_cons _ _ _ (der_24438 v h) (hints_cons _ _ _ (der_24439 v h) (hints_cons _ _ _ (der_24440 v h) (hints_cons _ _ _ (der_24441 v h) (hints_cons _ _ _ (der_24442 v h) (hints_cons _ _ _ (der_24443 v h) (hints_cons _ _ _ (der_24444 v h) (hints_cons _ _ _ (der_24445 v h) (hints_cons _ _ _ (der_24446 v h) (hints_cons _ _ _ (der_24447 v h) (hints_cons _ _ _ (der_24448 v h) (hints_cons _ _ _ (der_24449 v h) (hints_cons _ _ _ (der_24450 v h) (hints_cons _ _ _ (der_24451 v h) (hints_cons _ _ _ (der_24452 v h) (hints_cons _ _ _ (der_24453 v h) (hints_cons _ _ _ (der_24454 v h) (hints_cons _ _ _ (der_24455 v h) (hints_cons _ _ _ (der_24456 v h) (hints_cons _ _ _ (der_24457 v h) (hints_cons _ _ _ (der_24458 v h) (hints_cons _ _ _ (der_24459 v h) (hints_cons _ _ _ (der_24460 v h) (hints_cons _ _ _ (der_24461 v h) (hints_cons _ _ _ (der_24462 v h) (hints_cons _ _ _ (der_24463 v h) (hints_cons _ _ _ (der_24464 v h) (hints_cons _ _ _ (der_24465 v h) (hints_cons _ _ _ (der_24466 v h) (hints_cons _ _ _ (der_24467 v h) (hints_cons _ _ _ (der_24468 v h) (hints_cons _ _ _ (der_24469 v h) (hints_cons _ _ _ (der_24470 v h) (hints_cons _ _ _ (der_24471 v h) (hints_cons _ _ _ (der_24472 v h) (hints_cons _ _ _ (der_24473 v h) (hints_cons _ _ _ (der_24474 v h) (hints_cons _ _ _ (der_24475 v h) (hints_cons _ _ _ (der_24476 v h) (hints_cons _ _ _ (der_24477 v h) (hints_cons _ _ _ (der_24478 v h) (hints_cons _ _ _ (der_24479 v h) (hints_cons _ _ _ (der_24480 v h) (hints_cons _ _ _ (der_24481 v h) (hints_cons _ _ _ (der_24482 v h) (hints_cons _ _ _ (der_24483 v h) (hints_cons _ _ _ (der_24484 v h) (hints_cons _ _ _ (der_24485 v h) (hints_cons _ _ _ (der_24486 v h) (hints_cons _ _ _ (der_24487 v h) (hints_cons _ _ _ (der_24488 v h) (hints_cons _ _ _ (der_24489 v h) (hints_cons _ _ _ (der_24490 v h) (hints_cons _ _ _ (der_24491 v h) (hints_cons _ _ _ (der_24492 v h) (hints_cons _ _ _ (der_24493 v h) (hints_cons _ _ _ (der_24494 v h) (hints_cons _ _ _ (der_24495 v h) (hints_cons _ _ _ (der_24496 v h) (hints_cons _ _ _ (der_24497 v h) (hints_cons _ _ _ (der_24498 v h) (hints_cons _ _ _ (der_24499 v h) (hints_cons _ _ _ (der_24500 v h) (hints_cons _ _ _ (der_24501 v h) (hints_cons _ _ _ (der_24502 v h) (hints_cons _ _ _ (der_24503 v h) (hints_cons _ _ _ (der_24504 v h) (hints_cons _ _ _ (der_24505 v h) (hints_cons _ _ _ (der_24506 v h) (hints_cons _ _ _ (der_24507 v h) (hints_cons _ _ _ (der_24508 v h) (hints_cons _ _ _ (der_24509 v h) (hints_cons _ _ _ (der_24510 v h) (hints_cons _ _ _ (der_24511 v h) (hints_cons _ _ _ (der_24512 v h) (hints_cons _ _ _ (der_24513 v h) (hints_cons _ _ _ (der_24514 v h) (hints_cons _ _ _ (der_24515 v h) (hints_cons _ _ _ (der_24516 v h) (hints_cons _ _ _ (der_24517 v h) (hints_cons _ _ _ (der_24518 v h) (hints_cons _ _ _ (der_24519 v h) (hints_cons _ _ _ (der_24520 v h) (hints_cons _ _ _ (der_24521 v h) (hints_cons _ _ _ (der_24522 v h) (hints_cons _ _ _ (der_24523 v h) (hints_cons _ _ _ (der_24524 v h) (hints_cons _ _ _ (der_24525 v h) (hints_cons _ _ _ (der_24526 v h) (hints_cons _ _ _ (der_24527 v h) (hints_cons _ _ _ (der_24528 v h) (hints_cons _ _ _ (der_24529 v h) (hints_cons _ _ _ (der_24530 v h) (hints_cons _ _ _ (der_24531 v h) (hints_cons _ _ _ (der_24532 v h) (hints_cons _ _ _ (der_24533 v h) (hints_cons _ _ _ (der_24534 v h) (hints_cons _ _ _ (der_24535 v h) (hints_cons _ _ _ (der_24536 v h) (hints_cons _ _ _ (der_24537 v h) (hints_cons _ _ _ (der_24538 v h) (hints_cons _ _ _ (der_24539 v h) (hints_cons _ _ _ (der_24540 v h) (hints_cons _ _ _ (der_24541 v h) (hints_cons _ _ _ (der_24542 v h) (hints_cons _ _ _ (der_24543 v h) (hints_cons _ _ _ (der_24544 v h) (hints_cons _ _ _ (der_24545 v h) (hints_cons _ _ _ (der_24546 v h) (hints_cons _ _ _ (der_24547 v h) (hints_cons _ _ _ (der_24548 v h) (hints_cons _ _ _ (der_24549 v h) (hints_cons _ _ _ (der_24550 v h) (hints_cons _ _ _ (der_24551 v h) (hints_cons _ _ _ (der_24552 v h) (hints_cons _ _ _ (der_24553 v h) (hints_cons _ _ _ (der_24554 v h) (hints_cons _ _ _ (der_24555 v h) (hints_cons _ _ _ (der_24556 v h) (hints_cons _ _ _ (der_24557 v h) (hints_cons _ _ _ (der_24558 v h) (hints_cons _ _ _ (der_24559 v h) (hints_cons _ _ _ (der_24560 v h) (hints_cons _ _ _ (der_24561 v h) (hints_cons _ _ _ (der_24562 v h) (hints_cons _ _ _ (der_24563 v h) (hints_cons _ _ _ (der_24564 v h) (hints_cons _ _ _ (der_24565 v h) (hints_cons _ _ _ (der_24566 v h) (hints_cons _ _ _ (der_24567 v h) (hints_cons _ _ _ (der_24568 v h) (hints_cons _ _ _ (der_24569 v h) (hints_cons _ _ _ (der_24570 v h) (hints_cons _ _ _ (der_24571 v h) (hints_cons _ _ _ (der_24572 v h) (hints_cons _ _ _ (der_24573 v h) (hints_cons _ _ _ (der_24574 v h) (hints_cons _ _ _ (der_24575 v h) (hints_cons _ _ _ (der_24576 v h) (hints_cons _ _ _ (der_24577 v h) (hints_cons _ _ _ (der_24578 v h) (hints_cons _ _ _ (der_24579 v h) (hints_cons _ _ _ (der_24580 v h) (hints_cons _ _ _ (der_24581 v h) (hints_cons _ _ _ (der_24582 v h) (hints_cons _ _ _ (der_24583 v h) (hints_cons _ _ _ (der_24584 v h) (hints_cons _ _ _ (der_24585 v h) (hints_cons _ _ _ (der_24586 v h) (hints_cons _ _ _ (der_24587 v h) (hints_cons _ _ _ (der_24588 v h) (hints_cons _ _ _ (der_24589 v h) (hints_cons _ _ _ (der_24590 v h) (hints_cons _ _ _ (der_24591 v h) (hints_cons _ _ _ (der_24592 v h) (hints_cons _ _ _ (der_24593 v h) (hints_cons _ _ _ (der_24594 v h) (hints_cons _ _ _ (der_24595 v h) (hints_cons _ _ _ (der_24596 v h) (hints_cons _ _ _ (der_24597 v h) (hints_cons _ _ _ (der_24598 v h) (hints_cons _ _ _ (der_24599 v h) (hints_cons _ _ _ (der_24600 v h) (hints_cons _ _ _ (der_24601 v h) (hints_cons _ _ _ (der_24602 v h) (hints_cons _ _ _ (der_24603 v h) (hints_cons _ _ _ (der_24604 v h) (hints_cons _ _ _ (der_24605 v h) (hints_cons _ _ _ (der_24606 v h) (hints_cons _ _ _ (der_24607 v h) (hints_cons _ _ _ (der_24608 v h) (hints_cons _ _ _ (der_24609 v h) (hints_cons _ _ _ (der_24610 v h) (hints_cons _ _ _ (der_24611 v h) (hints_cons _ _ _ (der_24612 v h) (hints_cons _ _ _ (der_24613 v h) (hints_cons _ _ _ (der_24614 v h) (hints_cons _ _ _ (der_24615 v h) (hints_cons _ _ _ (der_24616 v h) (hints_cons _ _ _ (der_24617 v h) (hints_cons _ _ _ (der_24618 v h) (hints_cons _ _ _ (der_24619 v h) (hints_cons _ _ _ (der_24620 v h) (hints_cons _ _ _ (der_24621 v h) (hints_cons _ _ _ (der_24622 v h) (hints_cons _ _ _ (der_24623 v h) (hints_cons _ _ _ (der_24624 v h) (hints_cons _ _ _ (der_24625 v h) (hints_cons _ _ _ (der_24626 v h) (hints_cons _ _ _ (der_24627 v h) (hints_cons _ _ _ (der_24628 v h) (hints_cons _ _ _ (der_24629 v h) (hints_cons _ _ _ (der_24630 v h) (hints_cons _ _ _ (der_24631 v h) (hints_cons _ _ _ (der_24632 v h) (hints_cons _ _ _ (der_24633 v h) (hints_cons _ _ _ (der_24634 v h) (hints_cons _ _ _ (der_24635 v h) (hints_cons _ _ _ (der_24636 v h) (hints_cons _ _ _ (der_24637 v h) (hints_cons _ _ _ (der_24638 v h) (hints_cons _ _ _ (der_24639 v h) (hints_cons _ _ _ (der_24640 v h) (hints_cons _ _ _ (der_24641 v h) (hints_cons _ _ _ (der_24642 v h) (hints_cons _ _ _ (der_24643 v h) (hints_cons _ _ _ (der_24644 v h) (hints_cons _ _ _ (der_24645 v h) (hints_cons _ _ _ (der_24646 v h) (hints_cons _ _ _ (der_24647 v h) (hints_cons _ _ _ (der_24648 v h) (hints_cons _ _ _ (der_24649 v h) (hints_cons _ _ _ (der_24650 v h) (hints_cons _ _ _ (der_24651 v h) (hints_cons _ _ _ (der_24652 v h) (hints_cons _ _ _ (der_24653 v h) (hints_cons _ _ _ (der_24654 v h) (hints_cons _ _ _ (der_24655 v h) (hints_cons _ _ _ (der_24656 v h) (hints_cons _ _ _ (der_24657 v h) (hints_cons _ _ _ (der_24658 v h) (hints_cons _ _ _ (der_24659 v h) (hints_cons _ _ _ (der_24660 v h) (hints_cons _ _ _ (der_24661 v h) (hints_cons _ _ _ (der_24662 v h) (hints_cons _ _ _ (der_24663 v h) (hints_cons _ _ _ (der_24664 v h) (hints_cons _ _ _ (der_24665 v h) (hints_cons _ _ _ (der_24666 v h) (hints_cons _ _ _ (der_24667 v h) (hints_cons _ _ _ (der_24668 v h) (hints_cons _ _ _ (der_24669 v h) (hints_cons _ _ _ (der_24670 v h) (hints_cons _ _ _ (der_24671 v h) (hints_cons _ _ _ (der_24672 v h) (hints_cons _ _ _ (der_24673 v h) (hints_cons _ _ _ (der_24674 v h) (hints_cons _ _ _ (der_24675 v h) (hints_cons _ _ _ (der_24676 v h) (hints_cons _ _ _ (der_24677 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix004 := prefix003 ++ chunk004
theorem prefix_sound004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix004, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound003 v h c hc
  · exact chunk_sound004 v h c hc
end Percolation.NReplay
