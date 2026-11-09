import BatchH208
import BatchH209
import BatchH210
import BatchH211
import BatchH212
import BatchH213
import BatchH214
import BatchH215
import BatchH216
import BatchH217
import BatchH218
import BatchH219
import BatchH220
import BatchH221
import BatchH222
import BatchH223
namespace TripleCertificates
def recordsGroupH13 : List Certificate := ((((recordsH208 ++ recordsH209) ++ (recordsH210 ++ recordsH211)) ++ ((recordsH212 ++ recordsH213) ++ (recordsH214 ++ recordsH215))) ++ (((recordsH216 ++ recordsH217) ++ (recordsH218 ++ recordsH219)) ++ ((recordsH220 ++ recordsH221) ++ (recordsH222 ++ recordsH223))))
theorem checkedGroupH13 : ∀ r ∈ recordsGroupH13, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH208 checkedH209) (mergeChecked checkedH210 checkedH211)) (mergeChecked (mergeChecked checkedH212 checkedH213) (mergeChecked checkedH214 checkedH215))) (mergeChecked (mergeChecked (mergeChecked checkedH216 checkedH217) (mergeChecked checkedH218 checkedH219)) (mergeChecked (mergeChecked checkedH220 checkedH221) (mergeChecked checkedH222 checkedH223))))
end TripleCertificates
