import pathlib,json,datetime,hashlib,urllib.request,urllib.error
out=pathlib.Path(__file__).resolve().parent
r=json.loads((out/'registry-screen.json').read_text());head=r['openai']['head']
paths=[p for p in r['openai']['hits'] if p.endswith('/build/sections/00-introduction.tex') or p.endswith('/build/sections/01-model-endpoint.tex') or p.endswith('/build/sections/introduction.tex') or p.endswith('/build/sections/endpoint.tex')]
results=[]
for i,p in enumerate(paths):
 url='https://raw.githubusercontent.com/openai/math/'+head+'/'+p
 entry={'url':url,'path':p,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'source-review/1.0'}),timeout=18) as f:
   b=f.read(4000000);entry.update(status=f.status,headers=dict(f.headers))
  dest=out/'registry-bodies'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  entry.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),file=str(dest.relative_to(out)))
  print(p);print(b.decode()[:2800])
 except Exception as e: entry['error']=str(e);print(entry)
 results.append(entry)
(out/'registry-more-bodies-provenance.json').write_text(json.dumps(results,indent=2))
