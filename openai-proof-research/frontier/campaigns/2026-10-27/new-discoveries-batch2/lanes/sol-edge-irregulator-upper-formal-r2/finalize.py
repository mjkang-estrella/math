import json,hashlib,re,zipfile
from pathlib import Path
r=Path(__file__).parent
p=r/'replay.py';s=p.read_text();needle="log=(dest/'logs/OriginAudit.log').read_text()"
s=s.replace(needle,'''# Check actual imported package origins against the complete hash inventory.
roots=[Path(p['path'])/'.lake/build/lib/lean' for p in pins['packages']]
expected={p['path'] for p in json.loads((dest/'dependency-hashes.json').read_text())}
actual=set()
for mod in (dest/'formal/dependencies.txt').read_text().splitlines():
 if mod in MODULES: continue
 rel=Path(*mod.split('.')).with_suffix('.olean')
 hits=[root/rel for root in roots if (root/rel).is_file()]
 if hits:
  assert len(hits)==1
  actual.add(str(hits[0]))
 else:
  assert (Path(pins['lean_binary']).parent.parent/'lib/lean'/rel).is_file(),mod
assert actual==expected,(len(actual),len(expected),sorted(actual-expected))
'''+needle)
p.write_text(s)
log=(r/'logs/OriginAudit.log').read_text()
count=int(re.search(r'AUDIT_TOTAL (\d+)',log)[1]); print('AUDIT TOTAL',count)
# Independently extract every actual declaration record, without assuming names.
rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',log,re.M|re.S)
assert len(rows)==count and len({x[1] for x in rows})==count
assert all(x[4:]==('false','false','false') for x in rows)
assert set().union(*(set(re.findall(r'[\w.]+',x[3])) for x in rows))<={'propext','Quot.sound','Classical.choice'}
(r/'audit-inventory.json').write_text(json.dumps([dict(zip(['module','name','actual_type','transitive_axioms','unsafe','partial','axiom'],x)) for x in rows],indent=2)+'\n')
print('NEW INTERFACES',[x[1] for x in rows if x[0].startswith('Upper')])
