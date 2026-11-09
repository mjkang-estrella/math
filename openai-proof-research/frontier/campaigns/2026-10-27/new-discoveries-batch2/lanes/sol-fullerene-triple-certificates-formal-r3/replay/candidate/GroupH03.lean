import BatchH048
import BatchH049
import BatchH050
import BatchH051
import BatchH052
import BatchH053
import BatchH054
import BatchH055
import BatchH056
import BatchH057
import BatchH058
import BatchH059
import BatchH060
import BatchH061
import BatchH062
import BatchH063
namespace TripleCertificates
def recordsGroupH03 : List Certificate := ((((recordsH048 ++ recordsH049) ++ (recordsH050 ++ recordsH051)) ++ ((recordsH052 ++ recordsH053) ++ (recordsH054 ++ recordsH055))) ++ (((recordsH056 ++ recordsH057) ++ (recordsH058 ++ recordsH059)) ++ ((recordsH060 ++ recordsH061) ++ (recordsH062 ++ recordsH063))))
theorem checkedGroupH03 : ∀ r ∈ recordsGroupH03, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH048 checkedH049) (mergeChecked checkedH050 checkedH051)) (mergeChecked (mergeChecked checkedH052 checkedH053) (mergeChecked checkedH054 checkedH055))) (mergeChecked (mergeChecked (mergeChecked checkedH056 checkedH057) (mergeChecked checkedH058 checkedH059)) (mergeChecked (mergeChecked checkedH060 checkedH061) (mergeChecked checkedH062 checkedH063))))
end TripleCertificates
