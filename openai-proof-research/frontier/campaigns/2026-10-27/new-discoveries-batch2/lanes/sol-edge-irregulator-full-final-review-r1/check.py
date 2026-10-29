from pathlib import Path
import json,hashlib,datetime,collections,shutil,re
r=Path(__file__).resolve().parent;b=r.parent.parent;root=b/'lanes/root-edge-irregulator-final-freeze-r1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=root/'CURRENT-REGISTRIES.json';meta=json.loads(c.read_text());out={}
for reg in ['omega','openai']:
 p=root/(reg+'-tree.txt');lines=p.read_text().splitlines();assert len(lines)==meta[reg]['entries'];assert sha(p)==meta[reg]['tree_sha256']
 rows={line.split('\t',1)[1]:line.split('\t',1)[0].split()[2] for line in lines}
 bodies=list((root/'current-bodies').rglob('*')) if reg=='omega' else [root/'openai-CONTENTS.md']
 checks=[]
 for body in bodies:
  if not body.is_file():continue
  name=body.relative_to(root/'current-bodies').as_posix() if reg=='omega' else 'CONTENTS.md'
  data=body.read_bytes();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  if name not in rows and reg=='openai':name='lean/docs/CONTENTS.md'
  assert rows[name]==blob,(name,blob)
  checks.append({'path':name,'sha256':sha(body),'blob':blob});dest=r/'registry'/reg/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(body,dest)
 delta=root/(reg+'-delta.txt');assert len(delta.read_text().splitlines())==meta[reg]['delta_lines']
 out[reg]={'head':meta[reg]['head'],'entries':len(lines),'tree_sha256':sha(p),'delta_sha256':sha(delta),'bodies':checks}
 shutil.copyfile(delta,r/(reg+'-delta.txt'))
(r/'registry-checks.json').write_text(json.dumps(out,indent=2))
# Independent literal enumeration, with no graph library or candidate helper.
e=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,4),(4,5),(5,6)]
def valid(edges,n,mask,skip_hub=False):
 d=[0]*n;kept=[uv for k,uv in enumerate(edges) if mask>>k&1]
 for u,v in kept:d[u]+=1;d[v]+=1
 return all(d[u]!=d[v] for u,v in kept if not(skip_hub and 6 in (u,v)))
local=[8-m.bit_count() for m in range(256) if valid(e,7,m,True)];assert min(local)==3
edges=[(1+6*i+u if u<6 else 0,1+6*i+v if v<6 else 0) for i in range(2) for u,v in e]
cost=collections.Counter(16-m.bit_count() for m in range(65536) if valid(edges,13,m));assert min(cost)==6 and cost[6]==28
for t in range(2,101):
 edges=[(1+6*i+u if u<6 else 0,1+6*i+v if v<6 else 0) for i in range(t) for u,v in e];assert len(set(tuple(sorted(x)) for x in edges))==8*t
 mask=sum(1<<k for k in range(8*t) if k%8 not in (0,2,6));assert valid(edges,6*t+1,mask)
(r/'checker-results.json').write_text(json.dumps({'local_admissible':len(local),'local_min':min(local),'t2_distribution':dict(cost),'witness_range':[2,100]},indent=2))
print('registry inventory/blob and independent exact checks PASS')
