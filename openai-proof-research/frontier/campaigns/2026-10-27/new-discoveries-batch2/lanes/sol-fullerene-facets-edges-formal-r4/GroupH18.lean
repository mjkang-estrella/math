import BatchH288
import BatchH289
import BatchH290
import BatchH291
import BatchH292
import BatchH293
import BatchH294
import BatchH295
import BatchH296
import BatchH297
import BatchH298
import BatchH299
import BatchH300
import BatchH301
import BatchH302
import BatchH303
namespace TripleCertificates
noncomputable def recordsGroupH18 : List Certificate := ((((recordsH288 ++ recordsH289) ++ (recordsH290 ++ recordsH291)) ++ ((recordsH292 ++ recordsH293) ++ (recordsH294 ++ recordsH295))) ++ (((recordsH296 ++ recordsH297) ++ (recordsH298 ++ recordsH299)) ++ ((recordsH300 ++ recordsH301) ++ (recordsH302 ++ recordsH303))))
theorem checkedGroupH18 : ∀ r ∈ recordsGroupH18, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH288 checkedH289) (mergeChecked checkedH290 checkedH291)) (mergeChecked (mergeChecked checkedH292 checkedH293) (mergeChecked checkedH294 checkedH295))) (mergeChecked (mergeChecked (mergeChecked checkedH296 checkedH297) (mergeChecked checkedH298 checkedH299)) (mergeChecked (mergeChecked checkedH300 checkedH301) (mergeChecked checkedH302 checkedH303))))
end TripleCertificates
