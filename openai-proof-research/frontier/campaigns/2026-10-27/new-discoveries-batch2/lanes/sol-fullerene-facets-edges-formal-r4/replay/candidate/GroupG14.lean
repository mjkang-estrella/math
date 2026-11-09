import BatchG224
import BatchG225
import BatchG226
import BatchG227
import BatchG228
import BatchG229
import BatchG230
import BatchG231
import BatchG232
import BatchG233
import BatchG234
import BatchG235
import BatchG236
import BatchG237
import BatchG238
import BatchG239
namespace TripleCertificates
noncomputable def recordsGroupG14 : List Certificate := ((((recordsG224 ++ recordsG225) ++ (recordsG226 ++ recordsG227)) ++ ((recordsG228 ++ recordsG229) ++ (recordsG230 ++ recordsG231))) ++ (((recordsG232 ++ recordsG233) ++ (recordsG234 ++ recordsG235)) ++ ((recordsG236 ++ recordsG237) ++ (recordsG238 ++ recordsG239))))
theorem checkedGroupG14 : ∀ r ∈ recordsGroupG14, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG224 checkedG225) (mergeChecked checkedG226 checkedG227)) (mergeChecked (mergeChecked checkedG228 checkedG229) (mergeChecked checkedG230 checkedG231))) (mergeChecked (mergeChecked (mergeChecked checkedG232 checkedG233) (mergeChecked checkedG234 checkedG235)) (mergeChecked (mergeChecked checkedG236 checkedG237) (mergeChecked checkedG238 checkedG239))))
end TripleCertificates
