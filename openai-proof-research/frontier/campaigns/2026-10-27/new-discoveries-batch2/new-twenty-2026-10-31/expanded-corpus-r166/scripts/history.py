import pathlib,json,re,hashlib
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
ids=json.loads((D/'reservation.json').read_text())['ids']; pat=re.compile(r'(?<!\d)('+'|'.join(map(str,ids))+r')(?!\d)');out=[]
for p in D.parents[1].rglob('*'):
 if D in p.parents or not p.is_file() or p.suffix not in ['.md','.json'] or any(x in p.parts for x in ['corpus','.lake','node_modules','sources','raw','registries']):continue
 if p.name in ['reservation.json','launch.json'] or p.stat().st_size>4000000:continue
 t=p.read_text(errors='replace');hits=[]
 for i,l in enumerate(t.splitlines(),1):
  if pat.search(l):hits.append({'line':i,'text':l[:600]})
 if hits:out.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':hits[:30]})
(D/'outputs/history.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:18000])
