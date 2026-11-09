module
public import InstanceG
public import Rank
import AllG
import BindingsG
import ListedG
import CompletionCore
set_option autoImplicit false
set_option warningAsError true
public section
noncomputable section
namespace FullereneGeometry
open TripleCertificates
theorem complete_triples_G (ids : Fin 3 → Fin 32)
 (hi : LinearIndependent ℝ (fun k => qG (ids k))) (x : E)
 (hf : x ∈ poly qG) (ha : ∀ k, dot (qG (ids k)) x=1) : x ∈ Set.range pG :=
 complete_real qG pG AG DG PG recordsG DposG qbindG pbindG checkedG coverageG ids hi x hf ha
theorem listed_vertices_G (v : Fin 60) :
 pG v ∈ poly qG ∧ ∃ ids : Fin 3 → Fin 32,
 (∀ k, dot (qG (ids k)) (pG v)=1) ∧
 (∀ y : E, (∀ k, dot (qG (ids k)) y=1) → y=pG v) := by
 rw [← pbindG v]
 fin_cases v
 · exact listed_real qG AG DG (PG 0) DposG qbindG 0 12 1 listedG00.2.1 listedG00.2.2
 · exact listed_real qG AG DG (PG 1) DposG qbindG 0 13 12 listedG01.2.1 listedG01.2.2
 · exact listed_real qG AG DG (PG 2) DposG qbindG 0 14 13 listedG02.2.1 listedG02.2.2
 · exact listed_real qG AG DG (PG 3) DposG qbindG 0 15 14 listedG03.2.1 listedG03.2.2
 · exact listed_real qG AG DG (PG 4) DposG qbindG 0 16 15 listedG04.2.1 listedG04.2.2
 · exact listed_real qG AG DG (PG 5) DposG qbindG 0 1 16 listedG05.2.1 listedG05.2.2
 · exact listed_real qG AG DG (PG 6) DposG qbindG 1 12 18 listedG06.2.1 listedG06.2.2
 · exact listed_real qG AG DG (PG 7) DposG qbindG 1 19 16 listedG07.2.1 listedG07.2.2
 · exact listed_real qG AG DG (PG 8) DposG qbindG 1 17 19 listedG08.2.1 listedG08.2.2
 · exact listed_real qG AG DG (PG 9) DposG qbindG 1 18 17 listedG09.2.1 listedG09.2.2
 · exact listed_real qG AG DG (PG 10) DposG qbindG 12 8 18 listedG10.2.1 listedG10.2.2
 · exact listed_real qG AG DG (PG 11) DposG qbindG 12 13 8 listedG11.2.1 listedG11.2.2
 · exact listed_real qG AG DG (PG 12) DposG qbindG 13 7 29 listedG12.2.1 listedG12.2.2
 · exact listed_real qG AG DG (PG 13) DposG qbindG 13 14 7 listedG13.2.1 listedG13.2.2
 · exact listed_real qG AG DG (PG 14) DposG qbindG 13 29 8 listedG14.2.1 listedG14.2.2
 · exact listed_real qG AG DG (PG 15) DposG qbindG 14 11 31 listedG15.2.1 listedG15.2.2
 · exact listed_real qG AG DG (PG 16) DposG qbindG 14 15 11 listedG16.2.1 listedG16.2.2
 · exact listed_real qG AG DG (PG 17) DposG qbindG 14 31 7 listedG17.2.1 listedG17.2.2
 · exact listed_real qG AG DG (PG 18) DposG qbindG 15 5 27 listedG18.2.1 listedG18.2.2
 · exact listed_real qG AG DG (PG 19) DposG qbindG 15 16 5 listedG19.2.1 listedG19.2.2
 · exact listed_real qG AG DG (PG 20) DposG qbindG 15 27 11 listedG20.2.1 listedG20.2.2
 · exact listed_real qG AG DG (PG 21) DposG qbindG 16 19 5 listedG21.2.1 listedG21.2.2
 · exact listed_real qG AG DG (PG 22) DposG qbindG 17 2 20 listedG22.2.1 listedG22.2.2
 · exact listed_real qG AG DG (PG 23) DposG qbindG 17 18 2 listedG23.2.1 listedG23.2.2
 · exact listed_real qG AG DG (PG 24) DposG qbindG 17 6 19 listedG24.2.1 listedG24.2.2
 · exact listed_real qG AG DG (PG 25) DposG qbindG 17 20 6 listedG25.2.1 listedG25.2.2
 · exact listed_real qG AG DG (PG 26) DposG qbindG 18 8 22 listedG26.2.1 listedG26.2.2
 · exact listed_real qG AG DG (PG 27) DposG qbindG 18 22 2 listedG27.2.1 listedG27.2.2
 · exact listed_real qG AG DG (PG 28) DposG qbindG 19 6 5 listedG28.2.1 listedG28.2.2
 · exact listed_real qG AG DG (PG 29) DposG qbindG 2 3 20 listedG29.2.1 listedG29.2.2
 · exact listed_real qG AG DG (PG 30) DposG qbindG 2 21 3 listedG30.2.1 listedG30.2.2
 · exact listed_real qG AG DG (PG 31) DposG qbindG 2 22 21 listedG31.2.1 listedG31.2.2
 · exact listed_real qG AG DG (PG 32) DposG qbindG 3 23 20 listedG32.2.1 listedG32.2.2
 · exact listed_real qG AG DG (PG 33) DposG qbindG 3 24 23 listedG33.2.1 listedG33.2.2
 · exact listed_real qG AG DG (PG 34) DposG qbindG 3 25 24 listedG34.2.1 listedG34.2.2
 · exact listed_real qG AG DG (PG 35) DposG qbindG 3 21 25 listedG35.2.1 listedG35.2.2
 · exact listed_real qG AG DG (PG 36) DposG qbindG 20 23 6 listedG36.2.1 listedG36.2.2
 · exact listed_real qG AG DG (PG 37) DposG qbindG 21 9 25 listedG37.2.1 listedG37.2.2
 · exact listed_real qG AG DG (PG 38) DposG qbindG 21 22 9 listedG38.2.1 listedG38.2.2
 · exact listed_real qG AG DG (PG 39) DposG qbindG 22 8 29 listedG39.2.1 listedG39.2.2
 · exact listed_real qG AG DG (PG 40) DposG qbindG 22 29 9 listedG40.2.1 listedG40.2.2
 · exact listed_real qG AG DG (PG 41) DposG qbindG 23 4 26 listedG41.2.1 listedG41.2.2
 · exact listed_real qG AG DG (PG 42) DposG qbindG 23 24 4 listedG42.2.1 listedG42.2.2
 · exact listed_real qG AG DG (PG 43) DposG qbindG 23 26 6 listedG43.2.1 listedG43.2.2
 · exact listed_real qG AG DG (PG 44) DposG qbindG 24 10 28 listedG44.2.1 listedG44.2.2
 · exact listed_real qG AG DG (PG 45) DposG qbindG 24 25 10 listedG45.2.1 listedG45.2.2
 · exact listed_real qG AG DG (PG 46) DposG qbindG 24 28 4 listedG46.2.1 listedG46.2.2
 · exact listed_real qG AG DG (PG 47) DposG qbindG 25 9 30 listedG47.2.1 listedG47.2.2
 · exact listed_real qG AG DG (PG 48) DposG qbindG 25 30 10 listedG48.2.1 listedG48.2.2
 · exact listed_real qG AG DG (PG 49) DposG qbindG 4 27 26 listedG49.2.1 listedG49.2.2
 · exact listed_real qG AG DG (PG 50) DposG qbindG 4 28 27 listedG50.2.1 listedG50.2.2
 · exact listed_real qG AG DG (PG 51) DposG qbindG 26 5 6 listedG51.2.1 listedG51.2.2
 · exact listed_real qG AG DG (PG 52) DposG qbindG 26 27 5 listedG52.2.1 listedG52.2.2
 · exact listed_real qG AG DG (PG 53) DposG qbindG 27 28 11 listedG53.2.1 listedG53.2.2
 · exact listed_real qG AG DG (PG 54) DposG qbindG 28 10 31 listedG54.2.1 listedG54.2.2
 · exact listed_real qG AG DG (PG 55) DposG qbindG 28 31 11 listedG55.2.1 listedG55.2.2
 · exact listed_real qG AG DG (PG 56) DposG qbindG 7 30 29 listedG56.2.1 listedG56.2.2
 · exact listed_real qG AG DG (PG 57) DposG qbindG 7 31 30 listedG57.2.1 listedG57.2.2
 · exact listed_real qG AG DG (PG 58) DposG qbindG 29 30 9 listedG58.2.1 listedG58.2.2
 · exact listed_real qG AG DG (PG 59) DposG qbindG 30 31 10 listedG59.2.1 listedG59.2.2
theorem complete_vertices_G : (poly qG).extremePoints ℝ = Set.range pG :=
 complete_vertices_of_triple_certificates qG pG complete_triples_G listed_vertices_G
end FullereneGeometry
