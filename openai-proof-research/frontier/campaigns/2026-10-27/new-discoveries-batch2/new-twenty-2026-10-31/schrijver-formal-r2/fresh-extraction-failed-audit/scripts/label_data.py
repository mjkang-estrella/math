from pathlib import Path
import json
r=Path(__file__).resolve().parent.parent
mods=[]
for j,start in enumerate(range(0,819,16)):
 count=min(16,819-start);name=f'Label27_{j:03}';mods.append(name)
 s='import LabelBlocks\nimport Tree27_000\nset_option autoImplicit false\nset_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nset_option exponentiation.threshold 200000\nnamespace Schrijver\n'
 s+=f'theorem {name}_checked : labelRangeCheck 819 maskAt27 Tree27_000.depths {start} {count} = true := by decide\nend Schrijver\n'
 (r/f'src/{name}.lean').write_text(s)
(r/'outputs/label-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
s=''.join('import '+m+'\n' for m in mods)+'\nnamespace Schrijver\n'
s+='theorem labels27_edge : ∀ u v, (indexedGraph 819 maskAt27).Adj u v → indexDepth Tree27_000.depths v ≤ indexDepth Tree27_000.depths u + 1 := by\n  intro u v he\n'
for j,start in enumerate(range(0,819,16)):
 count=min(16,819-start)
 if start+count<819:
  s+=f'  by_cases h{j} : u.val < {start+count}\n  · exact labelRangeCheck_sound _ _ _ _ _ Label27_{j:03}_checked u v (by omega) he\n'
 else:
  s+=f'  exact labelRangeCheck_sound _ _ _ _ _ Label27_{j:03}_checked u v (by have := u.isLt; omega) he\n'
d=json.loads((r/'outputs/certificate-27.json').read_text());a,b=d['pair']
s+=f'theorem indexed_distance8 : 8 ≤ (indexedGraph 819 maskAt27).dist (⟨{a}, by decide⟩) (⟨{b}, by decide⟩) := by\n'
s+=f'  have h := labels_lower_distance (indexDepth Tree27_000.depths) labels27_edge (a := (⟨{a}, by decide⟩ : Fin 819)) (b := (⟨{b}, by decide⟩ : Fin 819)) (by decide) (Tree27_000.sound.1.preconnected _ _)\n'
s+='  have hv : indexDepth Tree27_000.depths (⟨'+str(b)+', by decide⟩ : Fin 819) = 8 := by decide\n  rw [hv] at h\n  exact h\nend Schrijver\n'
(r/'src/LowerIndexed.lean').write_text('set_option exponentiation.threshold 200000\n'+s if False else s.replace('namespace Schrijver','set_option exponentiation.threshold 200000\nnamespace Schrijver',1))
