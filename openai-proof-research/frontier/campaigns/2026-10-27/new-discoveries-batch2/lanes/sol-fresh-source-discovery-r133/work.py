import sys,json,hashlib,time,urllib.request,urllib.error
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parent.parent
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
def utc():return time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
if sys.argv[1]=='context':
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',R/'sources/upstream.json',B/'lanes/root-r128-r129-handback/DECISION.md',B/'lanes/root-r128-r129-handback/R130-DECISION.md']
 rows=[]
 for i,p in enumerate(paths):
  b=p.read_bytes();n=f'sources/context-{i:02d}{p.suffix}';(L/n).write_bytes(b);rows.append(dict(path=str(p),copy=n,sha256=sha(b),bytes=len(b),read_utc=utc(),mutable=p.name=='NEXT.md'))
  if p.suffix=='.json':
   j=json.loads(b);print(p.name,'keys',list(j), 'accepted',[(x.get('number'),x.get('title'),x.get('scope')) for x in j.get('accepted',[])])
  elif p.name=='NEXT.md':
   print('NEXT last 12000 chars:',b[-12000:].decode())
 dump('context-receipts.json',rows)
elif sys.argv[1]=='fetch':
 url,name=sys.argv[2:];rec=dict(url=url,utc=utc())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as r:
   b=r.read(6000001);rec.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
  (L/'sources'/name).write_bytes(b);rec.update(copy='sources/'+name,sha256=sha(b),bytes=len(b),truncated=len(b)>6000000)
 except urllib.error.HTTPError as e:
  b=e.read(100000);(L/'sources'/name).write_bytes(b);rec.update(status=e.code,error=str(e),copy='sources/'+name,sha256=sha(b),bytes=len(b))
 except Exception as e:rec['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
elif sys.argv[1]=='manifest':
 rows=[]
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}:
   b=p.read_bytes();rows.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
 dump('finalmanifest.json',dict(utc=utc(),files=rows,self_excluded=True,verification_excluded=True))
elif sys.argv[1]=='verify':
 rows=json.loads((L/'finalmanifest.json').read_text())['files'];bad=[x['path'] for x in rows if sha((L/x['path']).read_bytes())!=x['sha256']]
 dump('manifest-verification.json',dict(utc=utc(),files=len(rows),bad=bad));print(len(rows),bad);assert not bad
