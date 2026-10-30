from pathlib import Path
import json,hashlib,datetime,urllib.request,urllib.parse,sys
L=Path(__file__).resolve().parent
B=L.parent.parent
def sha(x): return hashlib.sha256(x).hexdigest()
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def put(p,x):
 p=L/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(x)
def dump(p,x):put(p,(json.dumps(x,indent=2)+'\n').encode())
def get(url,name):
 r={'url':url,'utc':utc(),'name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as f:
   x=f.read(16000000);r.update(status=f.status,final_url=f.url,sha256=sha(x),bytes=len(x),headers=dict(f.headers));put('sources/'+name,x)
 except Exception as e:
  r['error']=repr(e)
  if hasattr(e,'read'):put('failures/'+name,e.read(1000000))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r.get('status'),url,r.get('error',''),r.get('bytes',''))
 return r
def init():
 bindings=[]
 files=['AGENTS.md','ledger.json','prior-campaign-context.json']
 files+=['lanes/root-r%d-handback/DECISION.md'%n for n in [209,210,211,212]]
 files+=['lanes/sol-fresh-source-discovery-r212/'+s for s in ['SUMMARY.md','discovery.md','qualified-original-index.json','alias-refresh.json','workflow-failures.json']]
 for n in [207,208,209,210]:
  for s in ['qualified-original-index.json','alias-refresh.json','history-refresh.json']:
   if (B/('lanes/sol-fresh-source-discovery-r%d/'%n+s)).exists(): files.append('lanes/sol-fresh-source-discovery-r%d/'%n+s)
 for p in B.glob('NEXT*'):files.append(str(p.relative_to(B)))
 for f in files:
  p=B/f;x=p.read_bytes();dest='administrative/'+f if f in ['ledger.json','prior-campaign-context.json'] or f.startswith('NEXT') else 'assigned/'+f
  put(dest,x);assert sha(p.read_bytes())==sha(x);bindings.append(dict(original=str(p),copy=dest,sha256=sha(x),kind='administrative snapshot only' if dest.startswith('administrative') else 'assigned historical'))
 guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 x=guard.read_bytes();put('guard-copy.py',x);bindings.append(dict(original=str(guard),copy='guard-copy.py',sha256=sha(x),kind='guard'))
 dump('bindings.json',bindings)
 print('snapshot',len(bindings))
if __name__=='__main__':
 if sys.argv[1]=='init':init()
 elif sys.argv[1]=='get':get(sys.argv[2],sys.argv[3])
