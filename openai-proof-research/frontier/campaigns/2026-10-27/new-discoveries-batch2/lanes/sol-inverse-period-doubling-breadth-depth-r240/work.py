from pathlib import Path
import hashlib,json,sys,subprocess,urllib.request,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x): (L/n).write_text(json.dumps(x,indent=2))
def freeze(p):
 h=sha(p); q=L/'frozen'/h/p.name; q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists(): q.write_bytes(p.read_bytes())
 assert sha(p)==h==sha(q)
 rec={'original':str(p),'copy':str(q),'sha256':h}
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return q
def fetch(url,name):
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research source verification (bounded single request)'})
  with urllib.request.urlopen(req,timeout=22) as r:
   data=r.read(12_000_001); assert len(data)<=12_000_000
  p=L/'downloads'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(data);q=freeze(p)
  rec={'url':url,'file':str(q),'sha256':sha(q),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 except Exception as e:rec={'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec);return rec
if __name__!='__main__':pass
elif sys.argv[1]=='init':
 for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'AGENTS.md',B.parents[3]/'AGENTS.md']:
  if p.exists():
   q=L/'administrative'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes())
 old=B/'lanes/sol-polynomial-basins-breadth-depth-r237'
 for name in ['SCOUTING.md','source-bindings.json','history-4.json','history-12.json']:
  p=old/name
  if p.exists():freeze(p)
 for p in old.glob('frozen/*/stip8*'):freeze(p)
 for p in old.glob('**/stip8.pdf'):
  if 'frozen' not in str(p):freeze(p)
 print('initialized'); print('\n'.join(str(p) for p in (L/'frozen').glob('*/*')))
elif sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
elif sys.argv[1]=='read':
 p=Path(sys.argv[2]);q=freeze(p)
 if q.suffix=='.pdf':
  out=L/'texts'/ (q.stem+'.txt');out.parent.mkdir(exist_ok=True);subprocess.run(['pdftotext','-layout',str(q),str(out)],check=True);print(out.read_text()[:110000])
 else:print(q.read_text()[:55000])
