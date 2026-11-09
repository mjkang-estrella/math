import BatchH256
import BatchH257
import BatchH258
import BatchH259
import BatchH260
import BatchH261
import BatchH262
import BatchH263
import BatchH264
import BatchH265
import BatchH266
import BatchH267
import BatchH268
import BatchH269
import BatchH270
import BatchH271
namespace TripleCertificates
def recordsGroupH16 : List Certificate := ((((recordsH256 ++ recordsH257) ++ (recordsH258 ++ recordsH259)) ++ ((recordsH260 ++ recordsH261) ++ (recordsH262 ++ recordsH263))) ++ (((recordsH264 ++ recordsH265) ++ (recordsH266 ++ recordsH267)) ++ ((recordsH268 ++ recordsH269) ++ (recordsH270 ++ recordsH271))))
theorem checkedGroupH16 : ∀ r ∈ recordsGroupH16, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH256 checkedH257) (mergeChecked checkedH258 checkedH259)) (mergeChecked (mergeChecked checkedH260 checkedH261) (mergeChecked checkedH262 checkedH263))) (mergeChecked (mergeChecked (mergeChecked checkedH264 checkedH265) (mergeChecked checkedH266 checkedH267)) (mergeChecked (mergeChecked checkedH268 checkedH269) (mergeChecked checkedH270 checkedH271))))
end TripleCertificates
