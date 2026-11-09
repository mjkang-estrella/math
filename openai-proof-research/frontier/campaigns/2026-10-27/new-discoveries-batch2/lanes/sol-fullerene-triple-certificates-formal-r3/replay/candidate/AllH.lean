import GroupH00
import GroupH01
import GroupH02
import GroupH03
import GroupH04
import GroupH05
import GroupH06
import GroupH07
import GroupH08
import GroupH09
import GroupH10
import GroupH11
import GroupH12
import GroupH13
import GroupH14
import GroupH15
import GroupH16
import GroupH17
import GroupH18
import GroupH19
import Domain
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace TripleCertificates
def recordsH : List Certificate := ((((recordsGroupH00 ++ recordsGroupH01) ++ (recordsGroupH02 ++ (recordsGroupH03 ++ recordsGroupH04))) ++ ((recordsGroupH05 ++ recordsGroupH06) ++ (recordsGroupH07 ++ (recordsGroupH08 ++ recordsGroupH09)))) ++ (((recordsGroupH10 ++ recordsGroupH11) ++ (recordsGroupH12 ++ (recordsGroupH13 ++ recordsGroupH14))) ++ ((recordsGroupH15 ++ recordsGroupH16) ++ (recordsGroupH17 ++ (recordsGroupH18 ++ recordsGroupH19)))))
theorem checkedH : ∀ r ∈ recordsH, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedGroupH00 checkedGroupH01) (mergeChecked checkedGroupH02 (mergeChecked checkedGroupH03 checkedGroupH04))) (mergeChecked (mergeChecked checkedGroupH05 checkedGroupH06) (mergeChecked checkedGroupH07 (mergeChecked checkedGroupH08 checkedGroupH09)))) (mergeChecked (mergeChecked (mergeChecked checkedGroupH10 checkedGroupH11) (mergeChecked checkedGroupH12 (mergeChecked checkedGroupH13 checkedGroupH14))) (mergeChecked (mergeChecked checkedGroupH15 checkedGroupH16) (mergeChecked checkedGroupH17 (mergeChecked checkedGroupH18 checkedGroupH19)))))
theorem coverageH : recordsH.map Certificate.ids = domain := by rfl
end TripleCertificates
