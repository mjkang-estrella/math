from pathlib import Path
import json
r=Path(__file__).resolve().parents[1]
levels=json.loads((r/'graph-extensions.json').read_text())['levels'];mods=[]
for prev,level in zip(levels,levels[1:]):
 n=prev['order'];targets='['+', '.join(map(str,level['graphs']))+']'
 for start in range(0,len(prev['graphs']),8):
  name=f'GraphClosure{n}_{start//8:03d}';mods.append(name)
  lines=['import GraphChecker','namespace Nut8.'+name,'def targets : List Nat := '+targets]
  for idx in range(start,min(start+8,len(prev['graphs']))):
   a=prev['graphs'][idx];cs=[c for c in level['extensions'] if c['source_index']==idx]
   rows=[f'({c["neighbors"]}, {level["graphs"][c["target_index"]]}, ['+', '.join(map(str,c['permutation']))+'])' for c in cs]
   lines+=['def certificates'+str(idx)+' : List (Nat × Nat × List Nat) := [',',\n'.join(rows),']','theorem closed'+str(idx)+' : extensionClosed '+str(n)+' '+str(a)+' targets certificates'+str(idx)+' = true := by','  decide +kernel']
  lines+=['end Nut8.'+name]
  (r/'formal'/(name+'.lean')).write_text('\n'.join(lines)+'\n')
(r/'closure-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
