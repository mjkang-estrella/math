import BatchH096
import BatchH097
import BatchH098
import BatchH099
import BatchH100
import BatchH101
import BatchH102
import BatchH103
import BatchH104
import BatchH105
import BatchH106
import BatchH107
import BatchH108
import BatchH109
import BatchH110
import BatchH111
namespace TripleCertificates
noncomputable def recordsGroupH06 : List Certificate := ((((recordsH096 ++ recordsH097) ++ (recordsH098 ++ recordsH099)) ++ ((recordsH100 ++ recordsH101) ++ (recordsH102 ++ recordsH103))) ++ (((recordsH104 ++ recordsH105) ++ (recordsH106 ++ recordsH107)) ++ ((recordsH108 ++ recordsH109) ++ (recordsH110 ++ recordsH111))))
theorem checkedGroupH06 : ∀ r ∈ recordsGroupH06, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH096 checkedH097) (mergeChecked checkedH098 checkedH099)) (mergeChecked (mergeChecked checkedH100 checkedH101) (mergeChecked checkedH102 checkedH103))) (mergeChecked (mergeChecked (mergeChecked checkedH104 checkedH105) (mergeChecked checkedH106 checkedH107)) (mergeChecked (mergeChecked checkedH108 checkedH109) (mergeChecked checkedH110 checkedH111))))
end TripleCertificates
