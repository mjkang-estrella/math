from fetch import get,D
import json,hashlib,re
repo='https://api.github.com/repos/the-omega-institute/trureturing'
h=json.loads((D/'sources/omega-head.json').read_text()); sha=h['sha']
get(('omega-root.json',repo+'/git/trees/'+h['commit']['tree']['sha']))
t=json.loads((D/'sources/omega-root.json').read_text())['tree']
for scope in ['D5','Problems']:
 e=next(x for x in t if x['path']==scope); get(('omega-'+scope+'.json',repo+'/git/trees/'+e['sha']+'?recursive=1'))
patterns=r'wheel|naisargik|cycle.?star|total.?cut|comma|kadar|hookpartition|framing|ulam|speyer|bergeron|motivic|hadamard|sumset|direction.?flip|lipschitz|vnumber|recolor|k.?chain'
out={'omega_head':sha,'openai_head':json.loads((D/'sources/openai-head.json').read_text())['sha'],'scope':'path screen only; matching bodies require further reading','trees':{}}
paths=[D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']
for p in paths:
 if not p.exists():continue
 b=p.read_bytes(); d=json.loads(b); out['trees'][str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'truncated':d.get('truncated'),'hits':[e['path'] for e in d.get('tree',[]) if re.search(patterns,e['path'],re.I)]}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
