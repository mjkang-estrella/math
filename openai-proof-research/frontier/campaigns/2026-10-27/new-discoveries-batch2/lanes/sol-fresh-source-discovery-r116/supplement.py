import sqlite3,re,json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];db=sqlite3.connect(L/'audit.sqlite')
db.execute('create index if not exists bysha on done(sha)')
pat=re.compile(rb'jca2591|jca33018|10[.]68381/jca33018|Convexity.of.Generators|Lp.like.paranorm|Mulholland|Matkowski|converse.{0,25}Minkowski',re.I)
n=hits=0
with (L/'exact-source-supplement.jsonl').open('w') as out:
 for path,sha in db.execute('select min(path),sha from done group by sha'):
  p=R/path;count=0;tail=b'';off=0
  with p.open('rb') as f:
   for b in iter(lambda:f.read(131072),b''):
    s=tail+b
    if count<3:
     for m in pat.finditer(s):
      out.write(json.dumps({'path':path,'sha256':sha,'offset':off-len(tail)+m.start(),'excerpt':s[max(0,m.start()-120):m.end()+300].decode('utf8','replace')})+'\n');count+=1
      if count>=3:break
    tail=b[-256:];off+=len(b)
  n+=1;hits+=bool(count)
print(json.dumps({'unique_hash_representatives':n,'hit_representatives':hits,'mapping':'audit.sqlite done maps every original path to SHA256; originals.jsonl adds mtime and bytes','gaps':'Excluded JSONL metadata/echo files and binary-only sources not semantically cleared'}))
