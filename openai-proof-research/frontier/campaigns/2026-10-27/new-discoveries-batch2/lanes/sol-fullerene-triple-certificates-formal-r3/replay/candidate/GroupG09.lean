import BatchG144
import BatchG145
import BatchG146
import BatchG147
import BatchG148
import BatchG149
import BatchG150
import BatchG151
import BatchG152
import BatchG153
import BatchG154
import BatchG155
import BatchG156
import BatchG157
import BatchG158
import BatchG159
namespace TripleCertificates
def recordsGroupG09 : List Certificate := ((((recordsG144 ++ recordsG145) ++ (recordsG146 ++ recordsG147)) ++ ((recordsG148 ++ recordsG149) ++ (recordsG150 ++ recordsG151))) ++ (((recordsG152 ++ recordsG153) ++ (recordsG154 ++ recordsG155)) ++ ((recordsG156 ++ recordsG157) ++ (recordsG158 ++ recordsG159))))
theorem checkedGroupG09 : ∀ r ∈ recordsGroupG09, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG144 checkedG145) (mergeChecked checkedG146 checkedG147)) (mergeChecked (mergeChecked checkedG148 checkedG149) (mergeChecked checkedG150 checkedG151))) (mergeChecked (mergeChecked (mergeChecked checkedG152 checkedG153) (mergeChecked checkedG154 checkedG155)) (mergeChecked (mergeChecked checkedG156 checkedG157) (mergeChecked checkedG158 checkedG159))))
end TripleCertificates
