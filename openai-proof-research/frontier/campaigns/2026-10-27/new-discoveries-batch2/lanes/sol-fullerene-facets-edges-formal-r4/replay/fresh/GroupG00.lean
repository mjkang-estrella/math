import BatchG000
import BatchG001
import BatchG002
import BatchG003
import BatchG004
import BatchG005
import BatchG006
import BatchG007
import BatchG008
import BatchG009
import BatchG010
import BatchG011
import BatchG012
import BatchG013
import BatchG014
import BatchG015
namespace TripleCertificates
noncomputable def recordsGroupG00 : List Certificate := ((((recordsG000 ++ recordsG001) ++ (recordsG002 ++ recordsG003)) ++ ((recordsG004 ++ recordsG005) ++ (recordsG006 ++ recordsG007))) ++ (((recordsG008 ++ recordsG009) ++ (recordsG010 ++ recordsG011)) ++ ((recordsG012 ++ recordsG013) ++ (recordsG014 ++ recordsG015))))
theorem checkedGroupG00 : ∀ r ∈ recordsGroupG00, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG000 checkedG001) (mergeChecked checkedG002 checkedG003)) (mergeChecked (mergeChecked checkedG004 checkedG005) (mergeChecked checkedG006 checkedG007))) (mergeChecked (mergeChecked (mergeChecked checkedG008 checkedG009) (mergeChecked checkedG010 checkedG011)) (mergeChecked (mergeChecked checkedG012 checkedG013) (mergeChecked checkedG014 checkedG015))))
end TripleCertificates
