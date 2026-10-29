import os,re,json,hashlib,time,sqlite3,urllib.request,sys
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]; B=L.parent.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(131072),b''):h.update(b)
 return h.hexdigest()
def save(n,x): (L/n).write_text(json.dumps(x,indent=2))
def audit():
 pat=re.compile(rb'varentropy|2111[.]06997|simplex.{0,35}(?:code|conjecture)|Gaussian.{0,30}product.{0,15}(?:inequality|conjecture)|strengthened.{0,30}concave',re.I)
 excluded=re.compile(r'inventory.content|required.content|semantic.hit|duplicate.corpus|cache.echo|corpus.echo|matched.excerpts|priority.hits|audit[.-](?:hits|matches)|screen[.-](?:hits|content)|supplement.content|exact.id.supplement|snippets|pathmap|manifest|exclusions',re.I)
 db=sqlite3.connect(L/'audit.sqlite');db.execute('create table if not exists bodies(h text primary key)')
 start=time.monotonic();n=u=0;complete=True
 with (L/'pathmap.jsonl').open('w') as pm,(L/'matches.jsonl').open('w') as out:
  for base,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=L]
   for name in files:
    p=Path(base,name); rel=str(p.relative_to(R))
    if excluded.search(name) or (re.search(r'sol-fresh-source-discovery-r11[123]/',rel) and p.suffix in {'.jsonl','.sqlite'}):continue
    if p.suffix.lower() not in {'.md','.txt','.tex','.py','.lean','.json','.jsonl','.html','.bib','.sh'}:continue
    # Explicit size bound also excludes generated unrecognised aggregates.
    if p.stat().st_size>12000000:continue
    h=sha(p); fresh=db.execute('insert or ignore into bodies values(?)',(h,)).rowcount;n+=1
    pm.write(json.dumps({'p':rel,'sha256':h,'new':bool(fresh)})+'\n')
    if fresh:
     u+=1;tail=b'';offset=0;hits=0
     with p.open('rb') as f:
      for b in iter(lambda:f.read(65536),b''):
       s=tail+b
       for m in pat.finditer(s):
        out.write(json.dumps({'p':rel,'sha256':h,'offset':offset-len(tail)+m.start(),'text':s[max(0,m.start()-180):m.end()+350].decode('utf8','replace')})+'\n');hits+=1
        if hits==3:break
       if hits==3:break
       tail=b[-512:];offset+=len(b)
    if time.monotonic()-start>180:complete=False;break
   if not complete:break
 db.commit();save('audit-receipt.json',{'paths':n,'bodies':u,'walk_complete':complete,'seconds':time.monotonic()-start,'scope':'bounded pattern scan; not full mathematical reading; excludes generated echoes, binaries and >12MB files'})
 print((L/'audit-receipt.json').read_text())
def freeze():
 (L/'sources').mkdir(exist_ok=True)
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',L.parent/'sol-fresh-source-discovery-r117/SUMMARY.md',L.parent/'sol-fresh-source-discovery-r117/discovery.md',L.parent/'root-r117-handback/ADOPTION.json',L.parent/'root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json',L.parent/'sol-renyi-registry-gap-closure-r3/intervals.json']
 a=[]
 for i,p in enumerate(paths):
  q=L/'sources'/('context-%02d'%i+p.suffix);q.write_bytes(p.read_bytes());a.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':sha(q),'mutable':p.name in {'NEXT.md','ledger.json'}})
 save('context-sources.json',a)
def fetch():
 for name,url in zip(sys.argv[2::2],sys.argv[3::2]):
  rec={'url':url,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'path':'sources/'+name}
  try:
   with urllib.request.urlopen(url,timeout=22) as r:
    b=r.read(8000001)
    if len(b)>8000000:raise ValueError('8MB cap')
    (L/'sources'/name).write_bytes(b);rec.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(json.dumps(rec))
  if rec.get('status') in {403,429}:break
if __name__=='__main__': {'audit':audit,'freeze':freeze,'fetch':fetch}[sys.argv[1]]()
