import re,json,hashlib,pathlib,urllib.request,concurrent.futures,datetime
ROOT=pathlib.Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i07_structures'
PIN=json.loads((ROOT/'sources/upstream.json').read_text())['commit']
selected={126,177,197,207,247,249,250,251,253,259,285,305,315,320}
s=(ROOT/'sources/CONTENTS.md').read_text();a=list(re.finditer(r'\*\*(\d+)\.',s));dirs={};blocks=[]
for i,m in enumerate(a):
 if int(m[1]) in selected:
  v=s[m.start():a[i+1].start() if i+1<len(a) else len(s)];blocks.append(v)
  for d in re.findall(r'(preprints/[^/]+)/',v):dirs[d]=int(m[1])
(OUT/'catalogue-selected.md').write_text('\n'.join(blocks))
t=json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']
paths=[z['path'] for z in t if z['type']=='blob' and z['path'].endswith(('.tex','.bib')) and '/'.join(z['path'].split('/')[:2]) in dirs]
def fetch(p):
 u=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}';dest=OUT/'upstream'/p
 try:
  data=urllib.request.urlopen(u,timeout=50).read();dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
  return dict(path=p,url=u,family=dirs['/'.join(p.split('/')[:2])],sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 except Exception as e:return dict(path=p,url=u,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:records=list(pool.map(fetch,paths))
(OUT/'retrieval-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/README.md','frontier/iterations/README.md','frontier/iterations/i05-crossfield.md','frontier/reviews/i05-crossfield-r2.md','frontier/scouts/discrete.md','frontier/reviews/frankl-direct-r2.md']
(OUT/'input-snapshot.json').write_text(json.dumps([dict(path=p,sha256=hashlib.sha256((ROOT/p).read_bytes()).hexdigest()) for p in inputs],indent=2)+'\n')
print(json.dumps(dict(files=len(records),success=sum('sha256'in x for x in records),errors=[x for x in records if 'error'in x]),indent=2))
