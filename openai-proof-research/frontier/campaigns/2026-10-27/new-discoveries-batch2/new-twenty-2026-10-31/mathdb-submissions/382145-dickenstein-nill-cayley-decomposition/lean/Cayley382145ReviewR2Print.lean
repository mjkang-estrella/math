import Cayley382145ReviewR2
import Cayley382145Sanity

/-! # Reviewer r2 statement-print probe (SEPARATELY LABELED; no declarations). -/

set_option pp.proofs false
#print Cayley382145.IsPrimitive
#print Cayley382145.latticeHull
#print Cayley382145.facetOffset
#print Cayley382145.facetFace
#print Cayley382145.IsFacetNormal
#print Cayley382145.adjointSet
#print Cayley382145.qCodegree
#print Cayley382145.cayleyEmbed
#print Cayley382145.realExt
#print Cayley382145.IsCayleySumIn
#print Cayley382145.DickensteinNillCayleyConjecture
#check @Cayley382145.dickensteinNill_cayley
#check @Cayley382145.dickensteinNillCayleyConjecture_holds
#check @Cayley382145.seg_cayley
#check @Cayley382145.seg_qCodegree
