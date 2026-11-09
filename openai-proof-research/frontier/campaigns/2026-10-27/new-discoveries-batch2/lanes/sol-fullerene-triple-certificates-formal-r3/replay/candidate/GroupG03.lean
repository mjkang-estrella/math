import BatchG048
import BatchG049
import BatchG050
import BatchG051
import BatchG052
import BatchG053
import BatchG054
import BatchG055
import BatchG056
import BatchG057
import BatchG058
import BatchG059
import BatchG060
import BatchG061
import BatchG062
import BatchG063
namespace TripleCertificates
def recordsGroupG03 : List Certificate := ((((recordsG048 ++ recordsG049) ++ (recordsG050 ++ recordsG051)) ++ ((recordsG052 ++ recordsG053) ++ (recordsG054 ++ recordsG055))) ++ (((recordsG056 ++ recordsG057) ++ (recordsG058 ++ recordsG059)) ++ ((recordsG060 ++ recordsG061) ++ (recordsG062 ++ recordsG063))))
theorem checkedGroupG03 : ∀ r ∈ recordsGroupG03, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG048 checkedG049) (mergeChecked checkedG050 checkedG051)) (mergeChecked (mergeChecked checkedG052 checkedG053) (mergeChecked checkedG054 checkedG055))) (mergeChecked (mergeChecked (mergeChecked checkedG056 checkedG057) (mergeChecked checkedG058 checkedG059)) (mergeChecked (mergeChecked checkedG060 checkedG061) (mergeChecked checkedG062 checkedG063))))
end TripleCertificates
