from setup import *
out=[]
for p in (HERE/'inputs').rglob('*.json'):
 # Frozen corpus is only 183MB; parse only responses which advertise a tree.
 with p.open('rb') as f:prefix=f.read(1500)
 if b'"tree": [' not in prefix and b'"tree":[' not in prefix:continue
 try:
  d=json.loads(p.read_text())
  if not isinstance(d,dict) or not isinstance(d.get('tree'),list):continue
  entries=d['tree'];out.append({'file':str(p.relative_to(HERE)),'sha':d.get('sha'),'truncated':d.get('truncated'),'entries':len(entries),'child_trees':[x for x in entries if x.get('type')=='tree'] if len(entries)<80 else [],'recursive_paths':any('/' in x.get('path','') for x in entries)})
 except Exception as e:out.append({'file':str(p.relative_to(HERE)),'error':str(e)})
save('tree-inventory.json',out)
print(json.dumps(out,indent=2))
