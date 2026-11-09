import BatchH224
import BatchH225
import BatchH226
import BatchH227
import BatchH228
import BatchH229
import BatchH230
import BatchH231
import BatchH232
import BatchH233
import BatchH234
import BatchH235
import BatchH236
import BatchH237
import BatchH238
import BatchH239
namespace TripleCertificates
def recordsGroupH14 : List Certificate := ((((recordsH224 ++ recordsH225) ++ (recordsH226 ++ recordsH227)) ++ ((recordsH228 ++ recordsH229) ++ (recordsH230 ++ recordsH231))) ++ (((recordsH232 ++ recordsH233) ++ (recordsH234 ++ recordsH235)) ++ ((recordsH236 ++ recordsH237) ++ (recordsH238 ++ recordsH239))))
theorem checkedGroupH14 : ∀ r ∈ recordsGroupH14, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH224 checkedH225) (mergeChecked checkedH226 checkedH227)) (mergeChecked (mergeChecked checkedH228 checkedH229) (mergeChecked checkedH230 checkedH231))) (mergeChecked (mergeChecked (mergeChecked checkedH232 checkedH233) (mergeChecked checkedH234 checkedH235)) (mergeChecked (mergeChecked checkedH236 checkedH237) (mergeChecked checkedH238 checkedH239))))
end TripleCertificates
