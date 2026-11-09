import BatchH080
import BatchH081
import BatchH082
import BatchH083
import BatchH084
import BatchH085
import BatchH086
import BatchH087
import BatchH088
import BatchH089
import BatchH090
import BatchH091
import BatchH092
import BatchH093
import BatchH094
import BatchH095
namespace TripleCertificates
noncomputable def recordsGroupH05 : List Certificate := ((((recordsH080 ++ recordsH081) ++ (recordsH082 ++ recordsH083)) ++ ((recordsH084 ++ recordsH085) ++ (recordsH086 ++ recordsH087))) ++ (((recordsH088 ++ recordsH089) ++ (recordsH090 ++ recordsH091)) ++ ((recordsH092 ++ recordsH093) ++ (recordsH094 ++ recordsH095))))
theorem checkedGroupH05 : ∀ r ∈ recordsGroupH05, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH080 checkedH081) (mergeChecked checkedH082 checkedH083)) (mergeChecked (mergeChecked checkedH084 checkedH085) (mergeChecked checkedH086 checkedH087))) (mergeChecked (mergeChecked (mergeChecked checkedH088 checkedH089) (mergeChecked checkedH090 checkedH091)) (mergeChecked (mergeChecked checkedH092 checkedH093) (mergeChecked checkedH094 checkedH095))))
end TripleCertificates
