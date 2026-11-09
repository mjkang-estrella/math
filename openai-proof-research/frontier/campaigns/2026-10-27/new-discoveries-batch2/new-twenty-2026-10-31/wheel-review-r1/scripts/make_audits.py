from pathlib import Path
import json
D=Path.cwd();mods=['Foundation','WheelWeights','CycleBounds','Matching','DeletionGrid','WheelProfile','LowerWeighted','UpperIndexed','UpperCycle','UpperFamilies','UpperCounts','UpperCoverage','UpperAttaining','Final']
for mod in mods:
 s=(D/'replay/formal'/('Audit'+mod+'.lean')).read_text()
 s=s.replace('BODY {ci.value? (allowOpaque := true)}','BODY_PRESENT {(ci.value? (allowOpaque := true)).isSome}\nKIND {match ci with | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"}')
 (D/'replay/formal'/('ReviewAudit'+mod+'.lean')).write_text(s)
(D/'replay/formal/ReviewRestatement.lean').write_text('''import Final
open scoped BigOperators
open WheelFormal
set_option autoImplicit false
-- Source-language restatement expands every potentially weakened wrapper.
theorem reviewer_source_statement (t : ℕ) (ht : 1 ≤ t) :
    sInf (Set.range (fun c : FractionalColouring
      ((wheel (2*t+1)).boxProd (wheel (2*t+1))) =>
        ∑ s, c.weight s)) =
    (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+(t:ℝ)+1) := by
  exact target_proved t ht
#print axioms reviewer_source_statement
''')
# Independent falsity, range omission, and wrong wheel-size controls.
controls={'False':'import Final\nexample : False := by exact WheelFormal.target_proved\n','WrongValue':'import Final\nopen WheelFormal\nexample : fracChromatic (wheelSquare 1) = 3 := by\n  have h := target_proved 1 (by norm_num)\n  norm_num at h ⊢\n  linarith\n','NoRange':'import Final\nopen WheelFormal\nexample (t : ℕ) : fracChromatic (wheelSquare t) = (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+t+1) := by\n  exact target_proved t\n'}
for n,s in controls.items():(D/'replay/formal'/('ReviewNegative'+n+'.lean')).write_text(s)
