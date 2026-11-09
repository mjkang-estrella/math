import BatchG064
import BatchG065
import BatchG066
import BatchG067
import BatchG068
import BatchG069
import BatchG070
import BatchG071
import BatchG072
import BatchG073
import BatchG074
import BatchG075
import BatchG076
import BatchG077
import BatchG078
import BatchG079
namespace TripleCertificates
def recordsGroupG04 : List Certificate := ((((recordsG064 ++ recordsG065) ++ (recordsG066 ++ recordsG067)) ++ ((recordsG068 ++ recordsG069) ++ (recordsG070 ++ recordsG071))) ++ (((recordsG072 ++ recordsG073) ++ (recordsG074 ++ recordsG075)) ++ ((recordsG076 ++ recordsG077) ++ (recordsG078 ++ recordsG079))))
theorem checkedGroupG04 : ∀ r ∈ recordsGroupG04, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG064 checkedG065) (mergeChecked checkedG066 checkedG067)) (mergeChecked (mergeChecked checkedG068 checkedG069) (mergeChecked checkedG070 checkedG071))) (mergeChecked (mergeChecked (mergeChecked checkedG072 checkedG073) (mergeChecked checkedG074 checkedG075)) (mergeChecked (mergeChecked checkedG076 checkedG077) (mergeChecked checkedG078 checkedG079))))
end TripleCertificates
