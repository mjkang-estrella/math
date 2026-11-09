import BatchG208
import BatchG209
import BatchG210
import BatchG211
import BatchG212
import BatchG213
import BatchG214
import BatchG215
import BatchG216
import BatchG217
import BatchG218
import BatchG219
import BatchG220
import BatchG221
import BatchG222
import BatchG223
namespace TripleCertificates
def recordsGroupG13 : List Certificate := ((((recordsG208 ++ recordsG209) ++ (recordsG210 ++ recordsG211)) ++ ((recordsG212 ++ recordsG213) ++ (recordsG214 ++ recordsG215))) ++ (((recordsG216 ++ recordsG217) ++ (recordsG218 ++ recordsG219)) ++ ((recordsG220 ++ recordsG221) ++ (recordsG222 ++ recordsG223))))
theorem checkedGroupG13 : ∀ r ∈ recordsGroupG13, checked AG DG PG r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedG208 checkedG209) (mergeChecked checkedG210 checkedG211)) (mergeChecked (mergeChecked checkedG212 checkedG213) (mergeChecked checkedG214 checkedG215))) (mergeChecked (mergeChecked (mergeChecked checkedG216 checkedG217) (mergeChecked checkedG218 checkedG219)) (mergeChecked (mergeChecked checkedG220 checkedG221) (mergeChecked checkedG222 checkedG223))))
end TripleCertificates
