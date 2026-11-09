from pathlib import Path
import re,json
r=Path(__file__).resolve().parent.parent
p=json.loads((r/'inputs/leads-review-r122/outputs/graph-28-12-certificate.json').read_text())
print(str(p['vertices'][:2]))
roots=[int(re.search(r'def root.*?:=\s*⟨(\d+)',(r/f'src/Tree28_{j:03}.lean').read_text()).group(1)) for j in range(116)]
masks=sorted(p['vertices'])
assert masks==sorted(masks)
ws=[]
for m in masks:
 for t in range(28):
  rot=((m<<t)|(m>>(28-t)))&((1<<28)-1)
  if rot in [masks[x] for x in roots]:
   ws.append((t,masks.index(rot)));break
 else:raise AssertionError(m)
(r/'outputs/rotation-witnesses-r4.json').write_text(json.dumps(ws))
mods=[]
for j,start in enumerate(range(0,3185,32)):
 chunk=ws[start:start+32];name=f'Rotation28_{j:03}';mods.append(name)
 s='import RotationCheck\nnamespace Schrijver\nset_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nset_option exponentiation.threshold 100000\n'
 s+=f'theorem {name}_checked : rotationChunkCheck {start} {len(chunk)} #['+','.join(str(t) for t,_ in chunk)+'] #['+','.join(str(v) for _,v in chunk)+'] = true := by decide\nend Schrijver\n'
 (r/f'src/{name}.lean').write_text(s)
s=''.join(f'import {m}\n' for m in mods)+'namespace Schrijver\nset_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nset_option exponentiation.threshold 100000\n'
s+='theorem indexed_rotation_coverage28 (i : Fin 3185) :\n    ∃ t : Fin 28, ∃ r : Fin 3185, r ∈ upperRoots28 ∧\n      rotateVertex t (indexedVertex maskAt28 masks28_valid_at i) =\n        indexedVertex maskAt28 masks28_valid_at r := by\n'
for j,m in enumerate(mods[:-1]):
 s+=f'  by_cases h{j} : i.val < {(j+1)*32}\n  · exact rotationChunk_sound {m}_checked i (by omega)\n'
s+=f'  exact rotationChunk_sound {mods[-1]}_checked i (by have := i.isLt; omega)\n'
s+='''
theorem rotation_coverage28_from_enumeration (h : Enumeration28) :
    RotationRepresentativeCoverage28 := by
  intro a
  obtain ⟨i, hi⟩ := (literalIso28 h).toEquiv.surjective a
  subst a
  exact indexed_rotation_coverage28 i

theorem mathdb_352827_round4_conditional (h27 : Enumeration27) (h28 : Enumeration28) :
    ¬ SchrijverUnitGap :=
  mathdb_352827_round3_conditional h27 h28 (rotation_coverage28_from_enumeration h28)
end Schrijver
'''
(r/'src/RotationCoverage28.lean').write_text(s)
(r/'outputs/new-modules-r4.json').write_text(json.dumps(['RotationCheck']+mods+['RotationCoverage28']))
