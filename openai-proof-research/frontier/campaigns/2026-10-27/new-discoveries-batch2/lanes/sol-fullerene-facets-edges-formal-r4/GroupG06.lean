import BatchG096
import BatchG097
import BatchG098
import BatchG099
import BatchG100
import BatchG101
import BatchG102
import BatchG103
import BatchG104
import BatchG105
import BatchG106
import BatchG107
import BatchG108
import BatchG109
import BatchG110
import BatchG111
namespace TripleCertificates
noncomputable def recordsGroupG06 : List Certificate := ((((recordsG096 ++ recordsG097) ++ (recordsG098 ++ recordsG099)) ++ ((recordsG100 ++ recordsG101) ++ (recordsG102 ++ recordsG103))) ++ (((recordsG104 ++ recordsG105) ++ (recordsG106 ++ recordsG107)) ++ ((recordsG108 ++ recordsG109) ++ (recordsG110 ++ recordsG111))))
theorem checkedGroupG06 : ∀ r ∈ recordsGroupG06, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG096 checkedG097) (mergeChecked checkedG098 checkedG099)) (mergeChecked (mergeChecked checkedG100 checkedG101) (mergeChecked checkedG102 checkedG103))) (mergeChecked (mergeChecked (mergeChecked checkedG104 checkedG105) (mergeChecked checkedG106 checkedG107)) (mergeChecked (mergeChecked checkedG108 checkedG109) (mergeChecked checkedG110 checkedG111))))
end TripleCertificates
