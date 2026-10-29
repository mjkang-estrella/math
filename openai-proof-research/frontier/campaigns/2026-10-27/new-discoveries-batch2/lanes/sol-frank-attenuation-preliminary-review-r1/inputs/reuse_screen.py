import sqlite3,sys,re,json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
old=L.parent/'sol-fresh-source-discovery-r133'
pat=re.compile(rb'2404[.]10654|Hungarian.{0,8}roulette|s11634-026-00709|Barbiero|Frank.{0,90}(?:attenuat|discret|correl)|p53[.]pdf|Kendall.{0,100}surface|Fern.ndez.{0,30}Trutschnig',re.I)
shard=int(sys.argv[1]);db=sqlite3.connect('file:'+str(old/'history.sqlite')+'?mode=ro',uri=True)
stats=dict(shard=shard,base=str(old/'history.sqlite'),full_body=True,cutoff=None,read=0,bytes=0,changed=[],missing=[],hits=0,role_omitted=0)
roles=re.compile(r'(?:tree|inventory|manifest|receipt|aliases|matches|screen|http|pathmap|hashes)',re.I)
with (L/f'screen-hits-{shard}.jsonl').open('w') as out:
 for h,p in db.execute('select h,path from bodies where rowid % 4 = ?',(shard,)):
  q=R/p
  if roles.search(q.name):stats['role_omitted']+=1;continue
  try:b=q.read_bytes()
  except OSError:stats['missing'].append(p);continue
  hh=hashlib.sha256(b).hexdigest();stats['read']+=1;stats['bytes']+=len(b)
  if hh!=h:stats['changed'].append(p)
  ms=list(pat.finditer(b))
  if ms:
   stats['hits']+=1;out.write(json.dumps(dict(path=p,sha256=hh,matches=len(ms),excerpts=[b[max(0,m.start()-150):m.end()+220].decode(errors='replace') for m in ms]))+'\n')
(L/f'screen-{shard}.json').write_text(json.dumps(stats,indent=2)+'\n')
print(stats)
