import BatchG160
import BatchG161
import BatchG162
import BatchG163
import BatchG164
import BatchG165
import BatchG166
import BatchG167
import BatchG168
import BatchG169
import BatchG170
import BatchG171
import BatchG172
import BatchG173
import BatchG174
import BatchG175
namespace TripleCertificates
noncomputable def recordsGroupG10 : List Certificate := ((((recordsG160 ++ recordsG161) ++ (recordsG162 ++ recordsG163)) ++ ((recordsG164 ++ recordsG165) ++ (recordsG166 ++ recordsG167))) ++ (((recordsG168 ++ recordsG169) ++ (recordsG170 ++ recordsG171)) ++ ((recordsG172 ++ recordsG173) ++ (recordsG174 ++ recordsG175))))
theorem checkedGroupG10 : ∀ r ∈ recordsGroupG10, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG160 checkedG161) (mergeChecked checkedG162 checkedG163)) (mergeChecked (mergeChecked checkedG164 checkedG165) (mergeChecked checkedG166 checkedG167))) (mergeChecked (mergeChecked (mergeChecked checkedG168 checkedG169) (mergeChecked checkedG170 checkedG171)) (mergeChecked (mergeChecked checkedG172 checkedG173) (mergeChecked checkedG174 checkedG175))))
end TripleCertificates
