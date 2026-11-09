import BatchH144
import BatchH145
import BatchH146
import BatchH147
import BatchH148
import BatchH149
import BatchH150
import BatchH151
import BatchH152
import BatchH153
import BatchH154
import BatchH155
import BatchH156
import BatchH157
import BatchH158
import BatchH159
namespace TripleCertificates
noncomputable def recordsGroupH09 : List Certificate := ((((recordsH144 ++ recordsH145) ++ (recordsH146 ++ recordsH147)) ++ ((recordsH148 ++ recordsH149) ++ (recordsH150 ++ recordsH151))) ++ (((recordsH152 ++ recordsH153) ++ (recordsH154 ++ recordsH155)) ++ ((recordsH156 ++ recordsH157) ++ (recordsH158 ++ recordsH159))))
theorem checkedGroupH09 : ∀ r ∈ recordsGroupH09, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH144 checkedH145) (mergeChecked checkedH146 checkedH147)) (mergeChecked (mergeChecked checkedH148 checkedH149) (mergeChecked checkedH150 checkedH151))) (mergeChecked (mergeChecked (mergeChecked checkedH152 checkedH153) (mergeChecked checkedH154 checkedH155)) (mergeChecked (mergeChecked checkedH156 checkedH157) (mergeChecked checkedH158 checkedH159))))
end TripleCertificates
