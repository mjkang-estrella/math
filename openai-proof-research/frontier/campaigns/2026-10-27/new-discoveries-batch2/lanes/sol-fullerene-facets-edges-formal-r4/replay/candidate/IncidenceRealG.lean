import IncidenceCore
import IncidenceFactsG
import BindingsG
import IncidenceG00
import IncidenceG01
import IncidenceG02
import IncidenceG03
import IncidenceG04
import IncidenceG05
import IncidenceG06
import IncidenceG07
import IncidenceG08
import IncidenceG09
import IncidenceG10
import IncidenceG11
import IncidenceG12
import IncidenceG13
import IncidenceG14
import IncidenceG15
import IncidenceG16
import IncidenceG17
import IncidenceG18
import IncidenceG19
import IncidenceG20
import IncidenceG21
import IncidenceG22
import IncidenceG23
import IncidenceG24
import IncidenceG25
import IncidenceG26
import IncidenceG27
import IncidenceG28
import IncidenceG29
import IncidenceG30
import IncidenceG31
noncomputable section
namespace FullereneGeometry
open TripleCertificates
theorem real_incidence_G (i : Fin 32) (v : Fin 60) :
 v ∈ incidentG i ↔ dot (qG i) (pG v) = 1 := by
 have hh := active_iff_dot qG pG AG DG PG DposG qbindG pbindG positiveG i v
 have hc : active (AG i) DG (PG v) ↔ v ∈ incidentG i := by
  fin_cases i
  · exact incidenceG00 v
  · exact incidenceG01 v
  · exact incidenceG02 v
  · exact incidenceG03 v
  · exact incidenceG04 v
  · exact incidenceG05 v
  · exact incidenceG06 v
  · exact incidenceG07 v
  · exact incidenceG08 v
  · exact incidenceG09 v
  · exact incidenceG10 v
  · exact incidenceG11 v
  · exact incidenceG12 v
  · exact incidenceG13 v
  · exact incidenceG14 v
  · exact incidenceG15 v
  · exact incidenceG16 v
  · exact incidenceG17 v
  · exact incidenceG18 v
  · exact incidenceG19 v
  · exact incidenceG20 v
  · exact incidenceG21 v
  · exact incidenceG22 v
  · exact incidenceG23 v
  · exact incidenceG24 v
  · exact incidenceG25 v
  · exact incidenceG26 v
  · exact incidenceG27 v
  · exact incidenceG28 v
  · exact incidenceG29 v
  · exact incidenceG30 v
  · exact incidenceG31 v
 exact hc.symm.trans hh
theorem points_injective_G : Function.Injective pG := by
 intro v w h
 apply injectiveG v w
 apply same_of_real_eq _ _ (positiveG v) (positiveG w)
 simpa only [pbindG] using h
end FullereneGeometry
