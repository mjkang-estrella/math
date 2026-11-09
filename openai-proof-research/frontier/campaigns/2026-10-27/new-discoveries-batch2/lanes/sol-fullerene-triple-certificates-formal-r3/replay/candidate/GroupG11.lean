import BatchG176
import BatchG177
import BatchG178
import BatchG179
import BatchG180
import BatchG181
import BatchG182
import BatchG183
import BatchG184
import BatchG185
import BatchG186
import BatchG187
import BatchG188
import BatchG189
import BatchG190
import BatchG191
namespace TripleCertificates
def recordsGroupG11 : List Certificate := ((((recordsG176 ++ recordsG177) ++ (recordsG178 ++ recordsG179)) ++ ((recordsG180 ++ recordsG181) ++ (recordsG182 ++ recordsG183))) ++ (((recordsG184 ++ recordsG185) ++ (recordsG186 ++ recordsG187)) ++ ((recordsG188 ++ recordsG189) ++ (recordsG190 ++ recordsG191))))
theorem checkedGroupG11 : ∀ r ∈ recordsGroupG11, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG176 checkedG177) (mergeChecked checkedG178 checkedG179)) (mergeChecked (mergeChecked checkedG180 checkedG181) (mergeChecked checkedG182 checkedG183))) (mergeChecked (mergeChecked (mergeChecked checkedG184 checkedG185) (mergeChecked checkedG186 checkedG187)) (mergeChecked (mergeChecked checkedG188 checkedG189) (mergeChecked checkedG190 checkedG191))))
end TripleCertificates
