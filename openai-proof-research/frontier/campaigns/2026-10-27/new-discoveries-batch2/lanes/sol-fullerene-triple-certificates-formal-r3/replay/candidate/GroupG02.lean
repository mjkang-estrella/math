import BatchG032
import BatchG033
import BatchG034
import BatchG035
import BatchG036
import BatchG037
import BatchG038
import BatchG039
import BatchG040
import BatchG041
import BatchG042
import BatchG043
import BatchG044
import BatchG045
import BatchG046
import BatchG047
namespace TripleCertificates
def recordsGroupG02 : List Certificate := ((((recordsG032 ++ recordsG033) ++ (recordsG034 ++ recordsG035)) ++ ((recordsG036 ++ recordsG037) ++ (recordsG038 ++ recordsG039))) ++ (((recordsG040 ++ recordsG041) ++ (recordsG042 ++ recordsG043)) ++ ((recordsG044 ++ recordsG045) ++ (recordsG046 ++ recordsG047))))
theorem checkedGroupG02 : ∀ r ∈ recordsGroupG02, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG032 checkedG033) (mergeChecked checkedG034 checkedG035)) (mergeChecked (mergeChecked checkedG036 checkedG037) (mergeChecked checkedG038 checkedG039))) (mergeChecked (mergeChecked (mergeChecked checkedG040 checkedG041) (mergeChecked checkedG042 checkedG043)) (mergeChecked (mergeChecked checkedG044 checkedG045) (mergeChecked checkedG046 checkedG047))))
end TripleCertificates
