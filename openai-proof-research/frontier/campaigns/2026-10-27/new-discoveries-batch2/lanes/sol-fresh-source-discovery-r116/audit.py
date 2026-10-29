import os,re,json,hashlib,time,sqlite3
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]
db=sqlite3.connect(L/'audit.sqlite')
db.execute('create table if not exists done(path text primary key,size integer,mtime integer,sha text)')
pat=re.compile(rb'Matkowski|paranorm|Mulholland|converse.{0,20}Minkowski|2507[.]01353|jca2591|Radon.partition|Gaussian.convex.hull|Ter.Saakov',re.I)
gen=re.compile(r'inventory.content|required.content|supplement.content|screen.content|semantic.hits?|duplicate.corpus|screen.hits?|screen.hit.excerpts|target.hit.excerpts|audit.matches|audit.hits|semantic.supplement|exact.id.supplement|(?:inventory|required|supplement|screen).hashes|audit.manifest|audit.exclusions|audit.excluded|late.echo|[.]sqlite|[.]jsonl$',re.I)
start=time.monotonic(); n=sz=hit=ex=0;complete=True
with (L/'originals.jsonl').open('a') as mf,(L/'matched-excerpts.jsonl').open('a') as hf,(L/'excluded-echoes.jsonl').open('a') as ef:
 for base,dirs,files in os.walk(R):
  dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=L]
  if time.monotonic()-start>175:complete=False;break
  for name in files:
   p=Path(base,name);rel=str(p.relative_to(R));st=p.stat()
   if gen.search(name):
    ef.write(json.dumps({'path':rel,'bytes':st.st_size,'reason':'generated metadata/match/archive stream excluded; no mathematical inference'})+'\n');ex+=1;continue
   if p.suffix.lower() not in {'.md','.txt','.tex','.py','.lean','.json','.html','.bib','.csv','.tsv','.sh'}:continue
   prev=db.execute('select size,mtime,sha from done where path=?',(rel,)).fetchone()
   if prev and prev[:2]==(st.st_size,st.st_mtime_ns):continue
   h=hashlib.sha256(); tail=b'';count=0;off=0
   with p.open('rb') as f:
    while True:
     b=f.read(131072)
     if not b:break
     h.update(b)
     if count<3:
      s=tail+b
      for m in pat.finditer(s):
       hf.write(json.dumps({'path':rel,'offset':off-len(tail)+m.start(),'excerpt':s[max(0,m.start()-120):m.end()+260].decode('utf8','replace')})+'\n');count+=1
       if count>=3:break
     tail=b[-256:];off+=len(b)
   sha=h.hexdigest();mf.write(json.dumps({'path':rel,'bytes':st.st_size,'mtime_ns':st.st_mtime_ns,'sha256':sha,'hits':count})+'\n')
   db.execute('insert or replace into done values(?,?,?,?)',(rel,st.st_size,st.st_mtime_ns,sha));n+=1;sz+=st.st_size;hit+=bool(count)
db.commit()
receipt={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'files_this_run':n,'bytes_this_run':sz,'hit_files':hit,'exclusions':ex,'complete':complete,'seconds':time.monotonic()-start,'total_paths':db.execute('select count(*) from done').fetchone()[0],'gaps':['PDF-only binaries without text; excluded JSONL may contain original notes: separate bounded original-note supplement required','live concurrent writes are not an immutable snapshot']}
with (L/'audit-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(receipt))
