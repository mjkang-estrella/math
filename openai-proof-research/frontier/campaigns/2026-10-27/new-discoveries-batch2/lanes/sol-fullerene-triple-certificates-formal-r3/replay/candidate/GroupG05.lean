import BatchG080
import BatchG081
import BatchG082
import BatchG083
import BatchG084
import BatchG085
import BatchG086
import BatchG087
import BatchG088
import BatchG089
import BatchG090
import BatchG091
import BatchG092
import BatchG093
import BatchG094
import BatchG095
namespace TripleCertificates
def recordsGroupG05 : List Certificate := ((((recordsG080 ++ recordsG081) ++ (recordsG082 ++ recordsG083)) ++ ((recordsG084 ++ recordsG085) ++ (recordsG086 ++ recordsG087))) ++ (((recordsG088 ++ recordsG089) ++ (recordsG090 ++ recordsG091)) ++ ((recordsG092 ++ recordsG093) ++ (recordsG094 ++ recordsG095))))
theorem checkedGroupG05 : ∀ r ∈ recordsGroupG05, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG080 checkedG081) (mergeChecked checkedG082 checkedG083)) (mergeChecked (mergeChecked checkedG084 checkedG085) (mergeChecked checkedG086 checkedG087))) (mergeChecked (mergeChecked (mergeChecked checkedG088 checkedG089) (mergeChecked checkedG090 checkedG091)) (mergeChecked (mergeChecked checkedG092 checkedG093) (mergeChecked checkedG094 checkedG095))))
end TripleCertificates
