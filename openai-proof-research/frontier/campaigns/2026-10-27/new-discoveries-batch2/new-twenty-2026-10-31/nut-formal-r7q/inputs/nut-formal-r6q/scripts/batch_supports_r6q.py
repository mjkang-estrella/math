from pathlib import Path
import re,json
r=Path(__file__).resolve().parents[1];modules=[]
for i in range(194):
 name=f'FiniteSupport{i:03}';p=r/'formal'/(name+'.lean');s=p.read_text();a=s.index('theorem signed_enumeration');b=s.index('theorem enumeration');c=s.index('theorem tree');d=s.index('theorem verified');ns=f'Nut8.{name}'
 data=f'SupportData{i:03}';modules.append(data)
 (r/'formal'/(data+'.lean')).write_text(s[:a]+s[c:d]+f'end {ns}\n')
 checks=re.findall(r'theorem signed_enumeration\d+ :.*?\n  decide \+kernel\n',s[a:b],re.S)
 groups=[]
 for k,start in enumerate(range(0,len(checks),4)):
  m=f'SignedSupport{i:03}_{k:03}';groups.append(m);modules.append(m)
  (r/'formal'/(m+'.lean')).write_text(f'import {data}\nset_option maxRecDepth 4096\nnamespace {ns}\n'+''.join(checks[start:start+4])+f'end {ns}\n')
 p.write_text('\n'.join('import '+m for m in [data]+groups)+f'\nset_option maxRecDepth 4096\nset_option linter.unusedSimpArgs false\nnamespace {ns}\n'+s[b:c]+s[d:]);modules.append(name)
(r/'support-modules.json').write_text(json.dumps(modules,indent=2)+'\n');print('Support modules',len(modules))
