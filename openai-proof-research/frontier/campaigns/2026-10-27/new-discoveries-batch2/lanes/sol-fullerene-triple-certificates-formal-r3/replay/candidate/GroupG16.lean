import BatchG256
import BatchG257
import BatchG258
import BatchG259
import BatchG260
import BatchG261
import BatchG262
import BatchG263
import BatchG264
import BatchG265
import BatchG266
import BatchG267
import BatchG268
import BatchG269
import BatchG270
import BatchG271
namespace TripleCertificates
def recordsGroupG16 : List Certificate := ((((recordsG256 ++ recordsG257) ++ (recordsG258 ++ recordsG259)) ++ ((recordsG260 ++ recordsG261) ++ (recordsG262 ++ recordsG263))) ++ (((recordsG264 ++ recordsG265) ++ (recordsG266 ++ recordsG267)) ++ ((recordsG268 ++ recordsG269) ++ (recordsG270 ++ recordsG271))))
theorem checkedGroupG16 : ∀ r ∈ recordsGroupG16, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG256 checkedG257) (mergeChecked checkedG258 checkedG259)) (mergeChecked (mergeChecked checkedG260 checkedG261) (mergeChecked checkedG262 checkedG263))) (mergeChecked (mergeChecked (mergeChecked checkedG264 checkedG265) (mergeChecked checkedG266 checkedG267)) (mergeChecked (mergeChecked checkedG268 checkedG269) (mergeChecked checkedG270 checkedG271))))
end TripleCertificates
