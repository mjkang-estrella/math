import GroupG00
import GroupG01
import GroupG02
import GroupG03
import GroupG04
import GroupG05
import GroupG06
import GroupG07
import GroupG08
import GroupG09
import GroupG10
import GroupG11
import GroupG12
import GroupG13
import GroupG14
import GroupG15
import GroupG16
import GroupG17
import GroupG18
import GroupG19
import Domain
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace TripleCertificates
def recordsG : List Certificate := ((((recordsGroupG00 ++ recordsGroupG01) ++ (recordsGroupG02 ++ (recordsGroupG03 ++ recordsGroupG04))) ++ ((recordsGroupG05 ++ recordsGroupG06) ++ (recordsGroupG07 ++ (recordsGroupG08 ++ recordsGroupG09)))) ++ (((recordsGroupG10 ++ recordsGroupG11) ++ (recordsGroupG12 ++ (recordsGroupG13 ++ recordsGroupG14))) ++ ((recordsGroupG15 ++ recordsGroupG16) ++ (recordsGroupG17 ++ (recordsGroupG18 ++ recordsGroupG19)))))
theorem checkedG : ∀ r ∈ recordsG, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedGroupG00 checkedGroupG01) (mergeChecked checkedGroupG02 (mergeChecked checkedGroupG03 checkedGroupG04))) (mergeChecked (mergeChecked checkedGroupG05 checkedGroupG06) (mergeChecked checkedGroupG07 (mergeChecked checkedGroupG08 checkedGroupG09)))) (mergeChecked (mergeChecked (mergeChecked checkedGroupG10 checkedGroupG11) (mergeChecked checkedGroupG12 (mergeChecked checkedGroupG13 checkedGroupG14))) (mergeChecked (mergeChecked checkedGroupG15 checkedGroupG16) (mergeChecked checkedGroupG17 (mergeChecked checkedGroupG18 checkedGroupG19)))))
theorem coverageG : recordsG.map Certificate.ids = domain := by rfl
end TripleCertificates
