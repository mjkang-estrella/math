import IncidenceCore
import IncidenceFactsH
import BindingsH
import IncidenceH00
import IncidenceH01
import IncidenceH02
import IncidenceH03
import IncidenceH04
import IncidenceH05
import IncidenceH06
import IncidenceH07
import IncidenceH08
import IncidenceH09
import IncidenceH10
import IncidenceH11
import IncidenceH12
import IncidenceH13
import IncidenceH14
import IncidenceH15
import IncidenceH16
import IncidenceH17
import IncidenceH18
import IncidenceH19
import IncidenceH20
import IncidenceH21
import IncidenceH22
import IncidenceH23
import IncidenceH24
import IncidenceH25
import IncidenceH26
import IncidenceH27
import IncidenceH28
import IncidenceH29
import IncidenceH30
import IncidenceH31
noncomputable section
namespace FullereneGeometry
open TripleCertificates
theorem real_incidence_H (i : Fin 32) (v : Fin 60) :
 v ∈ incidentH i ↔ dot (qH i) (pH v) = 1 := by
 have hh := active_iff_dot qH pH AH DH PH DposH qbindH pbindH positiveH i v
 have hc : active (AH i) DH (PH v) ↔ v ∈ incidentH i := by
  fin_cases i
  · exact incidenceH00 v
  · exact incidenceH01 v
  · exact incidenceH02 v
  · exact incidenceH03 v
  · exact incidenceH04 v
  · exact incidenceH05 v
  · exact incidenceH06 v
  · exact incidenceH07 v
  · exact incidenceH08 v
  · exact incidenceH09 v
  · exact incidenceH10 v
  · exact incidenceH11 v
  · exact incidenceH12 v
  · exact incidenceH13 v
  · exact incidenceH14 v
  · exact incidenceH15 v
  · exact incidenceH16 v
  · exact incidenceH17 v
  · exact incidenceH18 v
  · exact incidenceH19 v
  · exact incidenceH20 v
  · exact incidenceH21 v
  · exact incidenceH22 v
  · exact incidenceH23 v
  · exact incidenceH24 v
  · exact incidenceH25 v
  · exact incidenceH26 v
  · exact incidenceH27 v
  · exact incidenceH28 v
  · exact incidenceH29 v
  · exact incidenceH30 v
  · exact incidenceH31 v
 exact hc.symm.trans hh
theorem points_injective_H : Function.Injective pH := by
 intro v w h
 apply injectiveH v w
 apply same_of_real_eq _ _ (positiveH v) (positiveH w)
 simpa only [pbindH] using h
end FullereneGeometry
