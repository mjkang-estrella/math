import json,hashlib,re,gzip,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
base=L.parent/'sol-fresh-source-discovery-r172/registry-path-screen.json'
pat=re.compile(r'Conca|Power.?Sum|2409.?18906|Han.?Xiong|FractionalGaussian',re.I);out=[]
for r in json.loads(base.read_bytes())['records']:
 p=Path(r['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
 try:
  j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else [];hits=[x for x in items if pat.search(x.get('path',''))]
 except json.JSONDecodeError:
  items=s.splitlines();hits=[x for x in items if pat.search(x.split('\t')[-1])]
 out.append(dict(path=str(p),sha256=sha(b),entries=len(items),hits=hits))
(L/'registry-screen.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),input=str(base),sha256=sha(base.read_bytes()),records=out,limits='Cached tree inventories only, not current-head or body absence clearance. GitHub routes denied and not requested. Historical capped intervals/missing merge trees PARKED. Current exact public searches and actual source/companion bodies separate.'),indent=2)+'\n')
for k in [178,182]:
 for n in ['qualification-r170.json','retained-originals.json','original-copy-provenance.json']:
  p=L.parent/f'sol-fresh-source-discovery-r{k}'/n
  if p.exists():(L/f'inherited-r{k}-{n}').write_bytes(p.read_bytes())
print('cached entries',sum(r['entries'] for r in out),'hits',sum(len(r['hits']) for r in out))
