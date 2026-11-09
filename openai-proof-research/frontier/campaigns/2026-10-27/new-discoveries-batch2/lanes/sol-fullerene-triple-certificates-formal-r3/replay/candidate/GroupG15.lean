import BatchG240
import BatchG241
import BatchG242
import BatchG243
import BatchG244
import BatchG245
import BatchG246
import BatchG247
import BatchG248
import BatchG249
import BatchG250
import BatchG251
import BatchG252
import BatchG253
import BatchG254
import BatchG255
namespace TripleCertificates
def recordsGroupG15 : List Certificate := ((((recordsG240 ++ recordsG241) ++ (recordsG242 ++ recordsG243)) ++ ((recordsG244 ++ recordsG245) ++ (recordsG246 ++ recordsG247))) ++ (((recordsG248 ++ recordsG249) ++ (recordsG250 ++ recordsG251)) ++ ((recordsG252 ++ recordsG253) ++ (recordsG254 ++ recordsG255))))
theorem checkedGroupG15 : ∀ r ∈ recordsGroupG15, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG240 checkedG241) (mergeChecked checkedG242 checkedG243)) (mergeChecked (mergeChecked checkedG244 checkedG245) (mergeChecked checkedG246 checkedG247))) (mergeChecked (mergeChecked (mergeChecked checkedG248 checkedG249) (mergeChecked checkedG250 checkedG251)) (mergeChecked (mergeChecked checkedG252 checkedG253) (mergeChecked checkedG254 checkedG255))))
end TripleCertificates
