import BatchH064
import BatchH065
import BatchH066
import BatchH067
import BatchH068
import BatchH069
import BatchH070
import BatchH071
import BatchH072
import BatchH073
import BatchH074
import BatchH075
import BatchH076
import BatchH077
import BatchH078
import BatchH079
namespace TripleCertificates
noncomputable def recordsGroupH04 : List Certificate := ((((recordsH064 ++ recordsH065) ++ (recordsH066 ++ recordsH067)) ++ ((recordsH068 ++ recordsH069) ++ (recordsH070 ++ recordsH071))) ++ (((recordsH072 ++ recordsH073) ++ (recordsH074 ++ recordsH075)) ++ ((recordsH076 ++ recordsH077) ++ (recordsH078 ++ recordsH079))))
theorem checkedGroupH04 : ∀ r ∈ recordsGroupH04, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH064 checkedH065) (mergeChecked checkedH066 checkedH067)) (mergeChecked (mergeChecked checkedH068 checkedH069) (mergeChecked checkedH070 checkedH071))) (mergeChecked (mergeChecked (mergeChecked checkedH072 checkedH073) (mergeChecked checkedH074 checkedH075)) (mergeChecked (mergeChecked checkedH076 checkedH077) (mergeChecked checkedH078 checkedH079))))
end TripleCertificates
