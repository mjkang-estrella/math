import BatchH128
import BatchH129
import BatchH130
import BatchH131
import BatchH132
import BatchH133
import BatchH134
import BatchH135
import BatchH136
import BatchH137
import BatchH138
import BatchH139
import BatchH140
import BatchH141
import BatchH142
import BatchH143
namespace TripleCertificates
noncomputable def recordsGroupH08 : List Certificate := ((((recordsH128 ++ recordsH129) ++ (recordsH130 ++ recordsH131)) ++ ((recordsH132 ++ recordsH133) ++ (recordsH134 ++ recordsH135))) ++ (((recordsH136 ++ recordsH137) ++ (recordsH138 ++ recordsH139)) ++ ((recordsH140 ++ recordsH141) ++ (recordsH142 ++ recordsH143))))
theorem checkedGroupH08 : ∀ r ∈ recordsGroupH08, checked AH DH PH r := (mergeChecked (mergeChecked (mergeChecked (mergeChecked checkedH128 checkedH129) (mergeChecked checkedH130 checkedH131)) (mergeChecked (mergeChecked checkedH132 checkedH133) (mergeChecked checkedH134 checkedH135))) (mergeChecked (mergeChecked (mergeChecked checkedH136 checkedH137) (mergeChecked checkedH138 checkedH139)) (mergeChecked (mergeChecked checkedH140 checkedH141) (mergeChecked checkedH142 checkedH143))))
end TripleCertificates
