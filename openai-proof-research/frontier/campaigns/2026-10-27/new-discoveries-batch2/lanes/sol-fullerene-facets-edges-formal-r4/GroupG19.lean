import BatchG304
import BatchG305
import BatchG306
import BatchG307
import BatchG308
import BatchG309
namespace TripleCertificates
noncomputable def recordsGroupG19 : List Certificate := ((recordsG304 ++ (recordsG305 ++ recordsG306)) ++ (recordsG307 ++ (recordsG308 ++ recordsG309)))
theorem checkedGroupG19 : ∀ r ∈ recordsGroupG19, checked AG DG PG r := (mergeChecked (mergeChecked checkedG304 (mergeChecked checkedG305 checkedG306)) (mergeChecked checkedG307 (mergeChecked checkedG308 checkedG309)))
end TripleCertificates
