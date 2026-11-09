import BatchH240
import BatchH241
import BatchH242
import BatchH243
import BatchH244
import BatchH245
import BatchH246
import BatchH247
import BatchH248
import BatchH249
import BatchH250
import BatchH251
import BatchH252
import BatchH253
import BatchH254
import BatchH255
namespace TripleCertificates
noncomputable def recordsGroupH15 : List Certificate := ((((recordsH240 ++ recordsH241) ++ (recordsH242 ++ recordsH243)) ++ ((recordsH244 ++ recordsH245) ++ (recordsH246 ++ recordsH247))) ++ (((recordsH248 ++ recordsH249) ++ (recordsH250 ++ recordsH251)) ++ ((recordsH252 ++ recordsH253) ++ (recordsH254 ++ recordsH255))))
theorem checkedGroupH15 : ∀ r ∈ recordsGroupH15, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH240 checkedH241) (mergeChecked checkedH242 checkedH243)) (mergeChecked (mergeChecked checkedH244 checkedH245) (mergeChecked checkedH246 checkedH247))) (mergeChecked (mergeChecked (mergeChecked checkedH248 checkedH249) (mergeChecked checkedH250 checkedH251)) (mergeChecked (mergeChecked checkedH252 checkedH253) (mergeChecked checkedH254 checkedH255))))
end TripleCertificates
