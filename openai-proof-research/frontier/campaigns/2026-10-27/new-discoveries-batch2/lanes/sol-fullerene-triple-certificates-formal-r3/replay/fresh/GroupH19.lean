import BatchH304
import BatchH305
import BatchH306
import BatchH307
import BatchH308
import BatchH309
namespace TripleCertificates
noncomputable def recordsGroupH19 : List Certificate := ((recordsH304 ++ (recordsH305 ++ recordsH306)) ++ (recordsH307 ++ (recordsH308 ++ recordsH309)))
theorem checkedGroupH19 : ∀ r ∈ recordsGroupH19, checked AH DH PH r := (mergeChecked (mergeChecked checkedH304 (mergeChecked checkedH305 checkedH306)) (mergeChecked checkedH307 (mergeChecked checkedH308 checkedH309)))
end TripleCertificates
