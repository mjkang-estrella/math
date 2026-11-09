from pathlib import Path
import json,re
l=Path(__file__).resolve().parent
p=l/'extracted'
mods=list((p/'PDTAR').glob('*.lean'))
seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for m in re.findall(r'^import (PDTAR\.\w+)',(p/(n.replace('.','/')+'.lean')).read_text(),re.M):visit(m)
visit('PDTAR.FinalComplete')
hits=[]
for f in mods:
 for i,s in enumerate(f.read_text().splitlines(),1):
  if re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',s):hits.append([f.name,i,s])
r={'modules':len(mods),'closure':sorted(seen),'closure_equals_all':seen=={'PDTAR.'+f.stem for f in mods},'raw_token_hits':hits}
(l/'source-scan.json').write_text(json.dumps(r,indent=2)+'\n')
assert r['closure_equals_all'] and not hits
print(json.dumps(r,indent=2))
