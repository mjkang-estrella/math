from pathlib import Path
import json,re
r=Path(__file__).resolve().parents[1]
closure=json.loads((r/'closure.json').read_text())
tail=(r/'formal/AuditR5.lean').read_text().split('set_option pp.all true',1)[1]
tail='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option pp.all true'+tail
# No partial recursive auditor: bounded loops and Lean's collectAxioms.
audits=[]
for k,start in enumerate(range(0,len(closure),8)):
 group=closure[start:start+8];m=f'AuditFinal{k:03}';audits.append(m)
 body=re.sub(r'#\[`Nut, .*?\]\.contains m', '#['+', '.join('`'+m for m in group)+'].contains m',tail)
 (r/'formal'/(m+'.lean')).write_text('\n'.join('import '+m for m in group)+'\n'+body)
(r/'audit-modules.json').write_text(json.dumps(audits,indent=2)+'\n')
# Collect original negative controls without executing the inherited replay drivers.
import ast
controls={}
for lane in ['r6q','r6p']:
 tree=ast.parse((r/'inputs'/('nut-formal-'+lane)/'replay.py').read_text())
 for n in tree.body:
  if isinstance(n,ast.Assign):
   t=n.targets[0]
   if isinstance(t,ast.Name) and t.id=='controls':
    for key,val in zip(n.value.keys,n.value.values):
     if isinstance(val,ast.Constant):controls[ast.literal_eval(key)]=ast.literal_eval(val)
   if isinstance(t,ast.Subscript) and isinstance(t.value,ast.Name) and t.value.id=='controls':controls[ast.literal_eval(t.slice)]=ast.literal_eval(n.value)
controls['WrongDet']=(r/'formal/DetPilot.lean').read_text().replace('= 48 :=','= 49 :=')
(r/'negative-controls.json').write_text(json.dumps(controls,indent=2)+'\n')
