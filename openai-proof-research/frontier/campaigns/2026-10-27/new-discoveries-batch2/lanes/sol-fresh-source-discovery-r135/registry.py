import json,gzip,re,hashlib,sqlite3,sys
from pathlib import Path
from work import fetch
L=Path(__file__).resolve().parent;OLD=L.parent/'sol-fresh-source-discovery-r133';R=L.parents[5]
P=re.compile(rb'2408[.]13494|366901|2505[.]19642|368568|100945|weak.{0,25}metric|independent.{0,20}position|Nordhaus|PositionColour|PositionColor|Hamming',re.I)
if sys.argv[1]=='delta':
 d=json.loads((L/'sources/omega-compare.json').read_bytes())
 r=dict(base=d['base_commit']['sha'],head=json.loads((L/'sources/omega-head.json').read_bytes())['sha'],merge_base=d['merge_base_commit']['sha'],status=d['status'],ahead_by=d['ahead_by'],commits=len(d['commits']),files=len(d['files']),capped=len(d['files'])>=300 or len(d['commits'])>=250)
 r['paths']=[x['filename'] for x in d['files']];(L/'registry-delta.json').write_text(json.dumps(r,indent=2));print(r)
elif sys.argv[1]=='retained':
 db=sqlite3.connect('file:'+str(OLD/'history.sqlite')+'?mode=ro',uri=True);hits=[];n=0;lim=[];gone=[]
 # Full representative texts with registry-tree roles; retained index narrows
 # source inventories, not a semantic proof of no result.
 for h,p in db.execute('select h,path from bodies'):
  if not re.search(r'(?:omega|openai|trureturing).*(?:tree|paths)|(?:tree|paths).*(?:omega|openai|trureturing)',p,re.I):continue
  q=R/p
  try:
   if q.stat().st_size>12000000:lim.append(p);continue
   b=q.read_bytes();n+=1
   ms=list(P.finditer(b))
   if ms:hits.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest(),matches=[b[max(0,m.start()-100):m.end()+150].decode(errors='replace') for m in ms]))
  except OSError:gone.append(p)
 r=dict(full_bodies_read=n,hits=hits,oversized=lim,missing=gone,scope='retained representative registry tree/path texts only; exact aliases; no semantic absence; historical snapshots')
 (L/'registry-retained.json').write_text(json.dumps(r,indent=2));print('read',n,'hit bodies',len(hits),'oversize',lim)
 for j in hits:
  print(j['path'])
  for s in j['matches']:print(s)
