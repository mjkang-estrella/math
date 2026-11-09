import BatchG112
import BatchG113
import BatchG114
import BatchG115
import BatchG116
import BatchG117
import BatchG118
import BatchG119
import BatchG120
import BatchG121
import BatchG122
import BatchG123
import BatchG124
import BatchG125
import BatchG126
import BatchG127
namespace TripleCertificates
def recordsGroupG07 : List Certificate := ((((recordsG112 ++ recordsG113) ++ (recordsG114 ++ recordsG115)) ++ ((recordsG116 ++ recordsG117) ++ (recordsG118 ++ recordsG119))) ++ (((recordsG120 ++ recordsG121) ++ (recordsG122 ++ recordsG123)) ++ ((recordsG124 ++ recordsG125) ++ (recordsG126 ++ recordsG127))))
theorem checkedGroupG07 : ∀ r ∈ recordsGroupG07, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG112 checkedG113) (mergeChecked checkedG114 checkedG115)) (mergeChecked (mergeChecked checkedG116 checkedG117) (mergeChecked checkedG118 checkedG119))) (mergeChecked (mergeChecked (mergeChecked checkedG120 checkedG121) (mergeChecked checkedG122 checkedG123)) (mergeChecked (mergeChecked checkedG124 checkedG125) (mergeChecked checkedG126 checkedG127))))
end TripleCertificates
