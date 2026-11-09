import BatchH176
import BatchH177
import BatchH178
import BatchH179
import BatchH180
import BatchH181
import BatchH182
import BatchH183
import BatchH184
import BatchH185
import BatchH186
import BatchH187
import BatchH188
import BatchH189
import BatchH190
import BatchH191
namespace TripleCertificates
def recordsGroupH11 : List Certificate := ((((recordsH176 ++ recordsH177) ++ (recordsH178 ++ recordsH179)) ++ ((recordsH180 ++ recordsH181) ++ (recordsH182 ++ recordsH183))) ++ (((recordsH184 ++ recordsH185) ++ (recordsH186 ++ recordsH187)) ++ ((recordsH188 ++ recordsH189) ++ (recordsH190 ++ recordsH191))))
theorem checkedGroupH11 : ∀ r ∈ recordsGroupH11, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH176 checkedH177) (mergeChecked checkedH178 checkedH179)) (mergeChecked (mergeChecked checkedH180 checkedH181) (mergeChecked checkedH182 checkedH183))) (mergeChecked (mergeChecked (mergeChecked checkedH184 checkedH185) (mergeChecked checkedH186 checkedH187)) (mergeChecked (mergeChecked checkedH188 checkedH189) (mergeChecked checkedH190 checkedH191))))
end TripleCertificates
