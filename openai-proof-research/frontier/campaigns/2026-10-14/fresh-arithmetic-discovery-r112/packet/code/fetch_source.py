from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path(__file__).resolve().parents[1]
T=json.loads((R/'private/context/2-preprints-tree.json').read_text())
assert len(T['tree'])==13223 and not T['truncated']
assert hashlib.sha256((R/'private/context/2-preprints-tree.json').read_bytes()).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
families=['Nagatas-Conjecture-for-Plane-Curves-September-23-2026','Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026','Maximal-Multipoint-Seshadri-Constants-in-Higher-Dimensions-October-5-2026','Maximal-multipoint-Seshadri-constants-in-positive-characteristic-October-5-2026']
entries=[e for e in T['tree'] if e['type']=='blob' and e['path'].split('/')[1] in families and e['path'].endswith(('.tex','.bib','.md')) and '/provenance/' not in e['path']]
def fetch(e):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 try:
  with urllib.request.urlopen(url,timeout=40) as f:b=f.read()
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==e['size'] and blob==e['sha']
  p=R/'private/source'/e['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
  return dict(path=e['path'],url=url,size=len(b),git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),local=str(p.relative_to(R)))
 except Exception as x:return dict(path=e['path'],url=url,error=str(x))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(fetch,entries))
(R/'private/source/metadata.json').write_text(json.dumps(results,indent=2))
for x in results:print(x['path'],x.get('size',x.get('error')))
