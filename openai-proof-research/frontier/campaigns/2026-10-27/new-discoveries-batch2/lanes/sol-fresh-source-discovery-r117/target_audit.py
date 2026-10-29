import os,re,json,hashlib,sqlite3,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
pat=re.compile(rb'2606[.]13162|PanSkanderaWangAllSplits|Pan.{0,20}Skandera|2507[.]01332|inverse.{0,12}Z.{0,30}polynomial|2605[.]29151|Aluffi.{0,50}Chen|Grothendieck.{0,30}class|q.rook|Garsia.{0,10}Remmel',re.I)
gen=re.compile(r'inventory.content|required.content|semantic.hit|duplicate.corpus|cache.echo|corpus.echo|matched.excerpts|priority.hits|audit[.-](?:hits|matches)|screen[.-](?:hits|content)|supplement.content|exact.id.supplement|\.sqlite|^(?:originals|pathmap|priority-manifest|inventory|duplicate-manifest|excluded-echoes|exclusions|manifest|finalmanifest)[.]jsonl$',re.I)
db=sqlite3.connect(L/'target-audit.sqlite');db.execute('create table if not exists bodies(sha text primary key)')
start=time.monotonic();n=u=0;complete=True
with (L/'target-pathmap.jsonl').open('w') as pm,(L/'target-snippets.jsonl').open('w') as sn,(L/'target-exclusions.jsonl').open('w') as ex:
 for base,dirs,files in os.walk(R):
  dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=L]
  for name in files:
   p=Path(base,name);rel=str(p.relative_to(R))
   if gen.search(name) or (re.search(r'sol-fresh-source-discovery-r11[123]/',rel) and p.suffix in {'.jsonl','.sqlite'}):
    ex.write(json.dumps({'path':rel,'reason':'generated metadata/echo; not read as mathematics'})+'\n');continue
   if p.suffix.lower() not in {'.md','.txt','.tex','.py','.lean','.json','.jsonl','.html','.bib','.csv','.tsv','.sh'}:continue
   st=p.stat();h=hashlib.sha256()
   with p.open('rb') as f:
    for b in iter(lambda:f.read(262144),b''):
     h.update(b)
     if time.monotonic()-start>185:complete=False;break
   if not complete:break
   sha=h.hexdigest();fresh=db.execute('insert or ignore into bodies values(?)',(sha,)).rowcount;n+=1
   pm.write(json.dumps({'path':rel,'bytes':st.st_size,'sha256':sha,'unique':bool(fresh)})+'\n')
   if fresh:
    u+=1;tail=b'';offset=0;found=0
    with p.open('rb') as f:
     for b in iter(lambda:f.read(65536),b''):
      s=tail+b
      for m in pat.finditer(s):
       sn.write(json.dumps({'path':rel,'sha256':sha,'offset':offset-len(tail)+m.start(),'snippet':s[max(0,m.start()-100):m.end()+260].decode('utf8','replace')})+'\n');found+=1
       if found>=3:break
      if found>=3:break
      tail=b[-256:];offset+=len(b)
   if time.monotonic()-start>185:complete=False;break
  if not complete:break
db.commit();r={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'paths':n,'unique':u,'complete':complete,'seconds':time.monotonic()-start,'limits':['binary PDFs not read as mathematics','live concurrent writes not frozen','generated r111/r112/r113 JSONL excluded explicitly','metadata hashes/pathmaps are not mathematical evidence']}
(L/'target-audit-receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
