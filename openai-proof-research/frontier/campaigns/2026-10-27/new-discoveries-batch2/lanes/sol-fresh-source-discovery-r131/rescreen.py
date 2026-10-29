import sqlite3,re,json,sys,time,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
db=sqlite3.connect(L/'history.sqlite');shard=int(sys.argv[1]);pat=re.compile(rb'2409[.]14180|2601[.]03363|2507[.]08503|isolation.game|game.isolation|total.isolation|Henning.{0,30}Rall|Bre.{0,8}ar.{0,60}Dravec',re.I)
hits=[];n=0;t=time.monotonic()
for h,p in db.execute('select h,path from bodies where rowid % 4 = ?',(shard,)):
 b=(R/p).read_bytes();n+=1
 if pat.search(b):
  ex=[[m.start(),b[max(0,m.start()-160):m.end()+450].decode(errors='replace')] for m in pat.finditer(b)]
  hits.append(dict(path=p,sha256=h,matches=ex))
(L/f'isolation-screen-{shard}.json').write_text(json.dumps(dict(bodies=n,hits=hits,pattern=pat.pattern.decode(),seconds=time.monotonic()-t,global_cutoff=None,scope='Reuses all-date SHA256 bodies and complete aliases/format-role-size omissions from history scan; no extra directory exclusions.'),indent=2))
print(shard,n,'hits',len(hits));print(json.dumps(hits)[:13000])
