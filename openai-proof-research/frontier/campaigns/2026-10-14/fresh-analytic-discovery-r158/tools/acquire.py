from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
ROOT=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r158')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
entries=json.loads((ROOT/'private/tree-selection.json').read_text())
entries=[e for e in entries if '/figures/' not in e['path']]
def get(e):
 family='K4' if 'Every-four' in e['path'] else 'K3'
 rel=e['path'].split('/build/')[1]; p=ROOT/'private/source'/family/rel;p.parent.mkdir(parents=True,exist_ok=True)
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
 try:
  b=urllib.request.urlopen(url,timeout=45).read()
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  if len(b)!=e['size'] or blob!=e['sha']:raise ValueError('canonical mismatch')
  p.write_bytes(b)
  return dict(path=e['path'],copy=str(p.relative_to(ROOT)),url=url,size=len(b),gitblob=blob,sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:return dict(path=e['path'],error=str(ex))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:records=list(pool.map(get,entries))
(ROOT/'private/source-auth.json').write_text(json.dumps(records,indent=2)+'\n')
print('Authenticated',sum('error' not in x for x in records),'of',len(records),'objects;',sum(x.get('size',0) for x in records),'bytes')
for r in records:
 if 'error' in r:print(r)
