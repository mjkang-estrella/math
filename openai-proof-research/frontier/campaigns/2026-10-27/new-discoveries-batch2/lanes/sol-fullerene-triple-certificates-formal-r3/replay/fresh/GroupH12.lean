import BatchH192
import BatchH193
import BatchH194
import BatchH195
import BatchH196
import BatchH197
import BatchH198
import BatchH199
import BatchH200
import BatchH201
import BatchH202
import BatchH203
import BatchH204
import BatchH205
import BatchH206
import BatchH207
namespace TripleCertificates
noncomputable def recordsGroupH12 : List Certificate := ((((recordsH192 ++ recordsH193) ++ (recordsH194 ++ recordsH195)) ++ ((recordsH196 ++ recordsH197) ++ (recordsH198 ++ recordsH199))) ++ (((recordsH200 ++ recordsH201) ++ (recordsH202 ++ recordsH203)) ++ ((recordsH204 ++ recordsH205) ++ (recordsH206 ++ recordsH207))))
theorem checkedGroupH12 : ∀ r ∈ recordsGroupH12, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH192 checkedH193) (mergeChecked checkedH194 checkedH195)) (mergeChecked (mergeChecked checkedH196 checkedH197) (mergeChecked checkedH198 checkedH199))) (mergeChecked (mergeChecked (mergeChecked checkedH200 checkedH201) (mergeChecked checkedH202 checkedH203)) (mergeChecked (mergeChecked checkedH204 checkedH205) (mergeChecked checkedH206 checkedH207))))
end TripleCertificates
