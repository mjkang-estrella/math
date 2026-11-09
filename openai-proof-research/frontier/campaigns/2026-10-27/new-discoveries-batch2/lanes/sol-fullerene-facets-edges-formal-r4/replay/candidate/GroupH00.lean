import BatchH000
import BatchH001
import BatchH002
import BatchH003
import BatchH004
import BatchH005
import BatchH006
import BatchH007
import BatchH008
import BatchH009
import BatchH010
import BatchH011
import BatchH012
import BatchH013
import BatchH014
import BatchH015
namespace TripleCertificates
noncomputable def recordsGroupH00 : List Certificate := ((((recordsH000 ++ recordsH001) ++ (recordsH002 ++ recordsH003)) ++ ((recordsH004 ++ recordsH005) ++ (recordsH006 ++ recordsH007))) ++ (((recordsH008 ++ recordsH009) ++ (recordsH010 ++ recordsH011)) ++ ((recordsH012 ++ recordsH013) ++ (recordsH014 ++ recordsH015))))
theorem checkedGroupH00 : ∀ r ∈ recordsGroupH00, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH000 checkedH001) (mergeChecked checkedH002 checkedH003)) (mergeChecked (mergeChecked checkedH004 checkedH005) (mergeChecked checkedH006 checkedH007))) (mergeChecked (mergeChecked (mergeChecked checkedH008 checkedH009) (mergeChecked checkedH010 checkedH011)) (mergeChecked (mergeChecked checkedH012 checkedH013) (mergeChecked checkedH014 checkedH015))))
end TripleCertificates
