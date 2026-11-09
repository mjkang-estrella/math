import BatchH032
import BatchH033
import BatchH034
import BatchH035
import BatchH036
import BatchH037
import BatchH038
import BatchH039
import BatchH040
import BatchH041
import BatchH042
import BatchH043
import BatchH044
import BatchH045
import BatchH046
import BatchH047
namespace TripleCertificates
def recordsGroupH02 : List Certificate := ((((recordsH032 ++ recordsH033) ++ (recordsH034 ++ recordsH035)) ++ ((recordsH036 ++ recordsH037) ++ (recordsH038 ++ recordsH039))) ++ (((recordsH040 ++ recordsH041) ++ (recordsH042 ++ recordsH043)) ++ ((recordsH044 ++ recordsH045) ++ (recordsH046 ++ recordsH047))))
theorem checkedGroupH02 : ∀ r ∈ recordsGroupH02, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH032 checkedH033) (mergeChecked checkedH034 checkedH035)) (mergeChecked (mergeChecked checkedH036 checkedH037) (mergeChecked checkedH038 checkedH039))) (mergeChecked (mergeChecked (mergeChecked checkedH040 checkedH041) (mergeChecked checkedH042 checkedH043)) (mergeChecked (mergeChecked checkedH044 checkedH045) (mergeChecked checkedH046 checkedH047))))
end TripleCertificates
