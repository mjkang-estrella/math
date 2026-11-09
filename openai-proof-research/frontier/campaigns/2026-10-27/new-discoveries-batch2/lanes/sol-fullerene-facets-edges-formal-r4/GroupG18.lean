import BatchG288
import BatchG289
import BatchG290
import BatchG291
import BatchG292
import BatchG293
import BatchG294
import BatchG295
import BatchG296
import BatchG297
import BatchG298
import BatchG299
import BatchG300
import BatchG301
import BatchG302
import BatchG303
namespace TripleCertificates
noncomputable def recordsGroupG18 : List Certificate := ((((recordsG288 ++ recordsG289) ++ (recordsG290 ++ recordsG291)) ++ ((recordsG292 ++ recordsG293) ++ (recordsG294 ++ recordsG295))) ++ (((recordsG296 ++ recordsG297) ++ (recordsG298 ++ recordsG299)) ++ ((recordsG300 ++ recordsG301) ++ (recordsG302 ++ recordsG303))))
theorem checkedGroupG18 : ∀ r ∈ recordsGroupG18, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG288 checkedG289) (mergeChecked checkedG290 checkedG291)) (mergeChecked (mergeChecked checkedG292 checkedG293) (mergeChecked checkedG294 checkedG295))) (mergeChecked (mergeChecked (mergeChecked checkedG296 checkedG297) (mergeChecked checkedG298 checkedG299)) (mergeChecked (mergeChecked checkedG300 checkedG301) (mergeChecked checkedG302 checkedG303))))
end TripleCertificates
