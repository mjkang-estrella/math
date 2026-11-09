module
public import InstanceH
public import Rank
import AllH
import BindingsH
import ListedH
import CompletionCore
set_option autoImplicit false
set_option warningAsError true
public section
noncomputable section
namespace FullereneGeometry
open TripleCertificates
theorem complete_triples_H (ids : Fin 3 → Fin 32)
 (hi : LinearIndependent ℝ (fun k => qH (ids k))) (x : E)
 (hf : x ∈ poly qH) (ha : ∀ k, dot (qH (ids k)) x=1) : x ∈ Set.range pH :=
 complete_real qH pH AH DH PH recordsH DposH qbindH pbindH checkedH coverageH ids hi x hf ha
theorem listed_vertices_H (v : Fin 60) :
 pH v ∈ poly qH ∧ ∃ ids : Fin 3 → Fin 32,
 (∀ k, dot (qH (ids k)) (pH v)=1) ∧
 (∀ y : E, (∀ k, dot (qH (ids k)) y=1) → y=pH v) := by
 rw [← pbindH v]
 fin_cases v
 · exact listed_real qH AH DH (PH 0) DposH qbindH 0 12 1 listedH00.2.1 listedH00.2.2
 · exact listed_real qH AH DH (PH 1) DposH qbindH 0 13 12 listedH01.2.1 listedH01.2.2
 · exact listed_real qH AH DH (PH 2) DposH qbindH 0 14 13 listedH02.2.1 listedH02.2.2
 · exact listed_real qH AH DH (PH 3) DposH qbindH 0 15 14 listedH03.2.1 listedH03.2.2
 · exact listed_real qH AH DH (PH 4) DposH qbindH 0 16 15 listedH04.2.1 listedH04.2.2
 · exact listed_real qH AH DH (PH 5) DposH qbindH 0 1 16 listedH05.2.1 listedH05.2.2
 · exact listed_real qH AH DH (PH 6) DposH qbindH 1 12 18 listedH06.2.1 listedH06.2.2
 · exact listed_real qH AH DH (PH 7) DposH qbindH 1 19 16 listedH07.2.1 listedH07.2.2
 · exact listed_real qH AH DH (PH 8) DposH qbindH 1 17 19 listedH08.2.1 listedH08.2.2
 · exact listed_real qH AH DH (PH 9) DposH qbindH 1 18 17 listedH09.2.1 listedH09.2.2
 · exact listed_real qH AH DH (PH 10) DposH qbindH 12 8 18 listedH10.2.1 listedH10.2.2
 · exact listed_real qH AH DH (PH 11) DposH qbindH 12 13 8 listedH11.2.1 listedH11.2.2
 · exact listed_real qH AH DH (PH 12) DposH qbindH 13 7 29 listedH12.2.1 listedH12.2.2
 · exact listed_real qH AH DH (PH 13) DposH qbindH 13 14 7 listedH13.2.1 listedH13.2.2
 · exact listed_real qH AH DH (PH 14) DposH qbindH 13 29 8 listedH14.2.1 listedH14.2.2
 · exact listed_real qH AH DH (PH 15) DposH qbindH 14 11 31 listedH15.2.1 listedH15.2.2
 · exact listed_real qH AH DH (PH 16) DposH qbindH 14 15 11 listedH16.2.1 listedH16.2.2
 · exact listed_real qH AH DH (PH 17) DposH qbindH 14 31 7 listedH17.2.1 listedH17.2.2
 · exact listed_real qH AH DH (PH 18) DposH qbindH 15 5 27 listedH18.2.1 listedH18.2.2
 · exact listed_real qH AH DH (PH 19) DposH qbindH 15 16 5 listedH19.2.1 listedH19.2.2
 · exact listed_real qH AH DH (PH 20) DposH qbindH 15 27 11 listedH20.2.1 listedH20.2.2
 · exact listed_real qH AH DH (PH 21) DposH qbindH 16 19 5 listedH21.2.1 listedH21.2.2
 · exact listed_real qH AH DH (PH 22) DposH qbindH 17 2 20 listedH22.2.1 listedH22.2.2
 · exact listed_real qH AH DH (PH 23) DposH qbindH 17 18 2 listedH23.2.1 listedH23.2.2
 · exact listed_real qH AH DH (PH 24) DposH qbindH 17 6 19 listedH24.2.1 listedH24.2.2
 · exact listed_real qH AH DH (PH 25) DposH qbindH 17 20 6 listedH25.2.1 listedH25.2.2
 · exact listed_real qH AH DH (PH 26) DposH qbindH 18 8 22 listedH26.2.1 listedH26.2.2
 · exact listed_real qH AH DH (PH 27) DposH qbindH 18 22 2 listedH27.2.1 listedH27.2.2
 · exact listed_real qH AH DH (PH 28) DposH qbindH 19 26 5 listedH28.2.1 listedH28.2.2
 · exact listed_real qH AH DH (PH 29) DposH qbindH 19 6 26 listedH29.2.1 listedH29.2.2
 · exact listed_real qH AH DH (PH 30) DposH qbindH 2 3 20 listedH30.2.1 listedH30.2.2
 · exact listed_real qH AH DH (PH 31) DposH qbindH 2 21 3 listedH31.2.1 listedH31.2.2
 · exact listed_real qH AH DH (PH 32) DposH qbindH 2 22 21 listedH32.2.1 listedH32.2.2
 · exact listed_real qH AH DH (PH 33) DposH qbindH 3 23 20 listedH33.2.1 listedH33.2.2
 · exact listed_real qH AH DH (PH 34) DposH qbindH 3 24 23 listedH34.2.1 listedH34.2.2
 · exact listed_real qH AH DH (PH 35) DposH qbindH 3 25 24 listedH35.2.1 listedH35.2.2
 · exact listed_real qH AH DH (PH 36) DposH qbindH 3 21 25 listedH36.2.1 listedH36.2.2
 · exact listed_real qH AH DH (PH 37) DposH qbindH 20 23 6 listedH37.2.1 listedH37.2.2
 · exact listed_real qH AH DH (PH 38) DposH qbindH 21 9 25 listedH38.2.1 listedH38.2.2
 · exact listed_real qH AH DH (PH 39) DposH qbindH 21 22 9 listedH39.2.1 listedH39.2.2
 · exact listed_real qH AH DH (PH 40) DposH qbindH 22 8 29 listedH40.2.1 listedH40.2.2
 · exact listed_real qH AH DH (PH 41) DposH qbindH 22 29 9 listedH41.2.1 listedH41.2.2
 · exact listed_real qH AH DH (PH 42) DposH qbindH 23 4 26 listedH42.2.1 listedH42.2.2
 · exact listed_real qH AH DH (PH 43) DposH qbindH 23 24 4 listedH43.2.1 listedH43.2.2
 · exact listed_real qH AH DH (PH 44) DposH qbindH 23 26 6 listedH44.2.1 listedH44.2.2
 · exact listed_real qH AH DH (PH 45) DposH qbindH 24 10 28 listedH45.2.1 listedH45.2.2
 · exact listed_real qH AH DH (PH 46) DposH qbindH 24 25 10 listedH46.2.1 listedH46.2.2
 · exact listed_real qH AH DH (PH 47) DposH qbindH 24 28 4 listedH47.2.1 listedH47.2.2
 · exact listed_real qH AH DH (PH 48) DposH qbindH 25 9 30 listedH48.2.1 listedH48.2.2
 · exact listed_real qH AH DH (PH 49) DposH qbindH 25 30 10 listedH49.2.1 listedH49.2.2
 · exact listed_real qH AH DH (PH 50) DposH qbindH 4 27 26 listedH50.2.1 listedH50.2.2
 · exact listed_real qH AH DH (PH 51) DposH qbindH 4 28 27 listedH51.2.1 listedH51.2.2
 · exact listed_real qH AH DH (PH 52) DposH qbindH 26 27 5 listedH52.2.1 listedH52.2.2
 · exact listed_real qH AH DH (PH 53) DposH qbindH 27 28 11 listedH53.2.1 listedH53.2.2
 · exact listed_real qH AH DH (PH 54) DposH qbindH 28 10 31 listedH54.2.1 listedH54.2.2
 · exact listed_real qH AH DH (PH 55) DposH qbindH 28 31 11 listedH55.2.1 listedH55.2.2
 · exact listed_real qH AH DH (PH 56) DposH qbindH 7 30 29 listedH56.2.1 listedH56.2.2
 · exact listed_real qH AH DH (PH 57) DposH qbindH 7 31 30 listedH57.2.1 listedH57.2.2
 · exact listed_real qH AH DH (PH 58) DposH qbindH 29 30 9 listedH58.2.1 listedH58.2.2
 · exact listed_real qH AH DH (PH 59) DposH qbindH 30 31 10 listedH59.2.1 listedH59.2.2
theorem complete_vertices_H : (poly qH).extremePoints ℝ = Set.range pH :=
 complete_vertices_of_triple_certificates qH pH complete_triples_H listed_vertices_H
end FullereneGeometry
