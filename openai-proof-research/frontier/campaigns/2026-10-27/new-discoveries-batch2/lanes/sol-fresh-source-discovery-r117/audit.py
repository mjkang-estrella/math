import os,re,json,hashlib,sqlite3,time
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
db=sqlite3.connect(L/'audit.sqlite')
db.execute('create table if not exists paths(path text primary key,size integer,mtime integer,sha text)')
db.execute('create table if not exists bodies(sha text primary key)')
pat=re.compile(rb'2507[.]01332|inverse.{0,12}Z.{0,30}polynomial|2024LcotGcoM|Aluffi.{0,50}Chen|Grothendieck.{0,30}class|q.rook|Garsia.{0,10}Remmel|2606[.]13162|Permanental.Inequalities.and.Unit|Pan.{0,20}Skandera',re.I)
gen=re.compile(r'inventory.content|required.content|semantic.hit|duplicate.corpus|cache.echo|corpus.echo|matched.excerpts|priority.hits|audit[.-](?:hits|matches)|screen[.-](?:hits|content)|supplement.content|exact.id.supplement|\.sqlite|^(?:originals|pathmap|priority-manifest|inventory|duplicate-manifest|excluded-echoes|exclusions|manifest|finalmanifest)[.]jsonl$',re.I)
start=time.monotonic();n=0;unique=0;hits=0
with (L/'pathmap.jsonl').open('a') as out,(L/'exclusions.jsonl').open('a') as ex,(L/'snippets.jsonl').open('a') as sn:
 for base,dirs,files in os.walk(R):
  dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=L]
  for name in files:
   p=Path(base,name);rel=str(p.relative_to(R))
   if gen.search(name) or (re.search(r'sol-fresh-source-discovery-r11[123]/',rel) and re.search(r'corpus|echo|inventory|content|hits|matches',name,re.I)):
    ex.write(json.dumps({'path':rel,'reason':'generated echo/inventory; metadata only; not mathematics'})+'\n');continue
   if p.suffix.lower() not in {'.md','.txt','.tex','.py','.lean','.json','.jsonl','.html','.bib','.csv','.tsv','.sh'}:continue
   st=p.stat();old=db.execute('select size,mtime from paths where path=?',(rel,)).fetchone()
   if old==(st.st_size,st.st_mtime_ns):continue
   h=hashlib.sha256();tail=b'';offset=0;found=[]
   with p.open('rb') as f:
    for b in iter(lambda:f.read(65536),b''):
     h.update(b)
     if len(found)<3:
      s=tail+b
      for m in pat.finditer(s):
       found.append({'offset':offset-len(tail)+m.start(),'snippet':s[max(0,m.start()-100):m.end()+240].decode('utf8','replace')})
       if len(found)==3:break
     tail=b[-256:];offset+=len(b)
   sha=h.hexdigest();isnew=db.execute('insert or ignore into bodies values(?)',(sha,)).rowcount
   db.execute('insert or replace into paths values(?,?,?,?)',(rel,st.st_size,st.st_mtime_ns,sha))
   out.write(json.dumps({'path':rel,'bytes':st.st_size,'sha256':sha,'unique':bool(isnew)})+'\n')
   if isnew:
    unique+=1
    for x in found:sn.write(json.dumps(dict(path=rel,sha256=sha,**x))+'\n');hits+=1
   n+=1
   if n%2000==0:db.commit()
   if time.monotonic()-start>170:break
  if time.monotonic()-start>170:break
 db.commit()
receipt={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'paths_this_run':n,'unique_this_run':unique,'snippets':hits,'paths_total':db.execute('select count(*) from paths').fetchone()[0],'complete':time.monotonic()-start<=170,'seconds':time.monotonic()-start,'limits':'Original text streamed; binary PDFs not semantically read. Excluded generated echoes are not evidence. Live writes not frozen.'}
with (L/'audit-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(receipt))
