import BatchG192
import BatchG193
import BatchG194
import BatchG195
import BatchG196
import BatchG197
import BatchG198
import BatchG199
import BatchG200
import BatchG201
import BatchG202
import BatchG203
import BatchG204
import BatchG205
import BatchG206
import BatchG207
namespace TripleCertificates
def recordsGroupG12 : List Certificate := ((((recordsG192 ++ recordsG193) ++ (recordsG194 ++ recordsG195)) ++ ((recordsG196 ++ recordsG197) ++ (recordsG198 ++ recordsG199))) ++ (((recordsG200 ++ recordsG201) ++ (recordsG202 ++ recordsG203)) ++ ((recordsG204 ++ recordsG205) ++ (recordsG206 ++ recordsG207))))
theorem checkedGroupG12 : ∀ r ∈ recordsGroupG12, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG192 checkedG193) (mergeChecked checkedG194 checkedG195)) (mergeChecked (mergeChecked checkedG196 checkedG197) (mergeChecked checkedG198 checkedG199))) (mergeChecked (mergeChecked (mergeChecked checkedG200 checkedG201) (mergeChecked checkedG202 checkedG203)) (mergeChecked (mergeChecked checkedG204 checkedG205) (mergeChecked checkedG206 checkedG207))))
end TripleCertificates
