import BatchH160
import BatchH161
import BatchH162
import BatchH163
import BatchH164
import BatchH165
import BatchH166
import BatchH167
import BatchH168
import BatchH169
import BatchH170
import BatchH171
import BatchH172
import BatchH173
import BatchH174
import BatchH175
namespace TripleCertificates
noncomputable def recordsGroupH10 : List Certificate := ((((recordsH160 ++ recordsH161) ++ (recordsH162 ++ recordsH163)) ++ ((recordsH164 ++ recordsH165) ++ (recordsH166 ++ recordsH167))) ++ (((recordsH168 ++ recordsH169) ++ (recordsH170 ++ recordsH171)) ++ ((recordsH172 ++ recordsH173) ++ (recordsH174 ++ recordsH175))))
theorem checkedGroupH10 : ∀ r ∈ recordsGroupH10, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH160 checkedH161) (mergeChecked checkedH162 checkedH163)) (mergeChecked (mergeChecked checkedH164 checkedH165) (mergeChecked checkedH166 checkedH167))) (mergeChecked (mergeChecked (mergeChecked checkedH168 checkedH169) (mergeChecked checkedH170 checkedH171)) (mergeChecked (mergeChecked checkedH172 checkedH173) (mergeChecked checkedH174 checkedH175))))
end TripleCertificates
