import BatchH272
import BatchH273
import BatchH274
import BatchH275
import BatchH276
import BatchH277
import BatchH278
import BatchH279
import BatchH280
import BatchH281
import BatchH282
import BatchH283
import BatchH284
import BatchH285
import BatchH286
import BatchH287
namespace TripleCertificates
def recordsGroupH17 : List Certificate := ((((recordsH272 ++ recordsH273) ++ (recordsH274 ++ recordsH275)) ++ ((recordsH276 ++ recordsH277) ++ (recordsH278 ++ recordsH279))) ++ (((recordsH280 ++ recordsH281) ++ (recordsH282 ++ recordsH283)) ++ ((recordsH284 ++ recordsH285) ++ (recordsH286 ++ recordsH287))))
theorem checkedGroupH17 : ∀ r ∈ recordsGroupH17, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH272 checkedH273) (mergeChecked checkedH274 checkedH275)) (mergeChecked (mergeChecked checkedH276 checkedH277) (mergeChecked checkedH278 checkedH279))) (mergeChecked (mergeChecked (mergeChecked checkedH280 checkedH281) (mergeChecked checkedH282 checkedH283)) (mergeChecked (mergeChecked checkedH284 checkedH285) (mergeChecked checkedH286 checkedH287))))
end TripleCertificates
