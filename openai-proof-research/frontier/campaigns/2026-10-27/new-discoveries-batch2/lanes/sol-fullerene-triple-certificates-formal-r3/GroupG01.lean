import BatchG016
import BatchG017
import BatchG018
import BatchG019
import BatchG020
import BatchG021
import BatchG022
import BatchG023
import BatchG024
import BatchG025
import BatchG026
import BatchG027
import BatchG028
import BatchG029
import BatchG030
import BatchG031
namespace TripleCertificates
noncomputable def recordsGroupG01 : List Certificate := ((((recordsG016 ++ recordsG017) ++ (recordsG018 ++ recordsG019)) ++ ((recordsG020 ++ recordsG021) ++ (recordsG022 ++ recordsG023))) ++ (((recordsG024 ++ recordsG025) ++ (recordsG026 ++ recordsG027)) ++ ((recordsG028 ++ recordsG029) ++ (recordsG030 ++ recordsG031))))
theorem checkedGroupG01 : ∀ r ∈ recordsGroupG01, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG016 checkedG017) (mergeChecked checkedG018 checkedG019)) (mergeChecked (mergeChecked checkedG020 checkedG021) (mergeChecked checkedG022 checkedG023))) (mergeChecked (mergeChecked (mergeChecked checkedG024 checkedG025) (mergeChecked checkedG026 checkedG027)) (mergeChecked (mergeChecked checkedG028 checkedG029) (mergeChecked checkedG030 checkedG031))))
end TripleCertificates
