import json,hashlib,datetime
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');O=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r118/packet'
items=[('AGENTS.md',None),('sources/upstream.json',None),('frontier/NEW-TEN-2026-10-14.md',(1,180)),('sources/CONTENTS.md',(1,120)),('frontier/campaigns/2026-10-14/discovery-arithmetic-r117-parent/assessment.md',None)]
for name in ['notes/start.md','notes/feasibility.md','notes/finite-test-reduction.md','READING.md']:items.append(('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r117/packet/'+name,None))
for name in ['original-scope.md','proof-attempts.md','reading-limits.md']:items.append(('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r58/'+name,None))
items += [('frontier/reviews/geometry-mumford-review-r2.md',(136,175)),('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r96/REPORT.md',(22,22))]
h=lambda b:hashlib.sha256(b).hexdigest();rows=[]
for i,(path,extent) in enumerate(items,1):
 b=(ROOT/path).read_bytes();selected=b if extent is None else b''.join(b.splitlines(keepends=True)[extent[0]-1:extent[1]])
 dst='private/incoming/%02d.txt'%i;p=O/dst;p.parent.mkdir(exist_ok=True);p.write_bytes(selected)
 rows.append({'original_path':path,'original_size':len(b),'original_sha256':h(b),'selection_lines':extent,'copy_path':dst,'copy_size':len(selected),'copy_sha256':h(selected),'whole_copy':extent is None})
b=(ROOT/'sources/preprints-tree.json').read_bytes();t=json.loads(b)
assert h(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(t['tree'])==13223 and not t['truncated']
(O/'incoming-identities.json').write_text(json.dumps({'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'timing':'Late: after semantic reading and integrated reduction drafting; not initial-read byte stability. Whole originals and selected-copy membership are separate. No inherited archive manifests.','originals':rows,'tree':{'path':'sources/preprints-tree.json','size':len(b),'sha256':h(b),'entries':len(t['tree']),'truncated':t['truncated']}},indent=2))
print('Captured',len(rows),'inputs;',sum(r['whole_copy'] for r in rows),'whole copies')
