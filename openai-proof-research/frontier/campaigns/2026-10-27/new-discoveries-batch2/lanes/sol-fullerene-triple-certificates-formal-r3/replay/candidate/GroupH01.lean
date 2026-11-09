import BatchH016
import BatchH017
import BatchH018
import BatchH019
import BatchH020
import BatchH021
import BatchH022
import BatchH023
import BatchH024
import BatchH025
import BatchH026
import BatchH027
import BatchH028
import BatchH029
import BatchH030
import BatchH031
namespace TripleCertificates
def recordsGroupH01 : List Certificate := ((((recordsH016 ++ recordsH017) ++ (recordsH018 ++ recordsH019)) ++ ((recordsH020 ++ recordsH021) ++ (recordsH022 ++ recordsH023))) ++ (((recordsH024 ++ recordsH025) ++ (recordsH026 ++ recordsH027)) ++ ((recordsH028 ++ recordsH029) ++ (recordsH030 ++ recordsH031))))
theorem checkedGroupH01 : ∀ r ∈ recordsGroupH01, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH016 checkedH017) (mergeChecked checkedH018 checkedH019)) (mergeChecked (mergeChecked checkedH020 checkedH021) (mergeChecked checkedH022 checkedH023))) (mergeChecked (mergeChecked (mergeChecked checkedH024 checkedH025) (mergeChecked checkedH026 checkedH027)) (mergeChecked (mergeChecked checkedH028 checkedH029) (mergeChecked checkedH030 checkedH031))))
end TripleCertificates
