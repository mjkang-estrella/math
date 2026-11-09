import BatchH112
import BatchH113
import BatchH114
import BatchH115
import BatchH116
import BatchH117
import BatchH118
import BatchH119
import BatchH120
import BatchH121
import BatchH122
import BatchH123
import BatchH124
import BatchH125
import BatchH126
import BatchH127
namespace TripleCertificates
def recordsGroupH07 : List Certificate := ((((recordsH112 ++ recordsH113) ++ (recordsH114 ++ recordsH115)) ++ ((recordsH116 ++ recordsH117) ++ (recordsH118 ++ recordsH119))) ++ (((recordsH120 ++ recordsH121) ++ (recordsH122 ++ recordsH123)) ++ ((recordsH124 ++ recordsH125) ++ (recordsH126 ++ recordsH127))))
theorem checkedGroupH07 : ∀ r ∈ recordsGroupH07, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH112 checkedH113) (mergeChecked checkedH114 checkedH115)) (mergeChecked (mergeChecked checkedH116 checkedH117) (mergeChecked checkedH118 checkedH119))) (mergeChecked (mergeChecked (mergeChecked checkedH120 checkedH121) (mergeChecked checkedH122 checkedH123)) (mergeChecked (mergeChecked checkedH124 checkedH125) (mergeChecked checkedH126 checkedH127))))
end TripleCertificates
