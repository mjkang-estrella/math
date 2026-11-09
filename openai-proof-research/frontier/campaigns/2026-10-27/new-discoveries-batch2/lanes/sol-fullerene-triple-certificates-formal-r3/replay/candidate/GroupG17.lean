import BatchG272
import BatchG273
import BatchG274
import BatchG275
import BatchG276
import BatchG277
import BatchG278
import BatchG279
import BatchG280
import BatchG281
import BatchG282
import BatchG283
import BatchG284
import BatchG285
import BatchG286
import BatchG287
namespace TripleCertificates
def recordsGroupG17 : List Certificate := ((((recordsG272 ++ recordsG273) ++ (recordsG274 ++ recordsG275)) ++ ((recordsG276 ++ recordsG277) ++ (recordsG278 ++ recordsG279))) ++ (((recordsG280 ++ recordsG281) ++ (recordsG282 ++ recordsG283)) ++ ((recordsG284 ++ recordsG285) ++ (recordsG286 ++ recordsG287))))
theorem checkedGroupG17 : ∀ r ∈ recordsGroupG17, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG272 checkedG273) (mergeChecked checkedG274 checkedG275)) (mergeChecked (mergeChecked checkedG276 checkedG277) (mergeChecked checkedG278 checkedG279))) (mergeChecked (mergeChecked (mergeChecked checkedG280 checkedG281) (mergeChecked checkedG282 checkedG283)) (mergeChecked (mergeChecked checkedG284 checkedG285) (mergeChecked checkedG286 checkedG287))))
end TripleCertificates
