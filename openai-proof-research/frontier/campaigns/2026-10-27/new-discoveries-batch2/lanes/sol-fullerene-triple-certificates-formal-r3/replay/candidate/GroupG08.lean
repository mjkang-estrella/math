import BatchG128
import BatchG129
import BatchG130
import BatchG131
import BatchG132
import BatchG133
import BatchG134
import BatchG135
import BatchG136
import BatchG137
import BatchG138
import BatchG139
import BatchG140
import BatchG141
import BatchG142
import BatchG143
namespace TripleCertificates
def recordsGroupG08 : List Certificate := ((((recordsG128 ++ recordsG129) ++ (recordsG130 ++ recordsG131)) ++ ((recordsG132 ++ recordsG133) ++ (recordsG134 ++ recordsG135))) ++ (((recordsG136 ++ recordsG137) ++ (recordsG138 ++ recordsG139)) ++ ((recordsG140 ++ recordsG141) ++ (recordsG142 ++ recordsG143))))
theorem checkedGroupG08 : ∀ r ∈ recordsGroupG08, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG128 checkedG129) (mergeChecked checkedG130 checkedG131)) (mergeChecked (mergeChecked checkedG132 checkedG133) (mergeChecked checkedG134 checkedG135))) (mergeChecked (mergeChecked (mergeChecked checkedG136 checkedG137) (mergeChecked checkedG138 checkedG139)) (mergeChecked (mergeChecked checkedG140 checkedG141) (mergeChecked checkedG142 checkedG143))))
end TripleCertificates
