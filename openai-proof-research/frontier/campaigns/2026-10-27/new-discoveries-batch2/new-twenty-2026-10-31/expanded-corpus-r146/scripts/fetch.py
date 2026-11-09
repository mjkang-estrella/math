# Copied from expanded-corpus-r145 (adapted from r144). TLS verification left at default (on).
import json,pathlib,urllib.request,hashlib,datetime,sys,subprocess,time
D=pathlib.Path(__file__).resolve().parents[1]
args=sys.argv[1:]
kinds=['abs']
if args and args[0]=='--pdf':kinds=['pdf'];args=args[1:]
rows=json.loads((D/'reservation.json').read_text())['rows']
items=args or sorted({x['source_url'].split('/abs/')[-1] for x in rows})
for a in items:
 for kind in kinds:
  u=a if a.startswith('http') else f'https://arxiv.org/{kind}/{a}';p=D/'sources'/((a.split('//')[-1].replace('/','_')[:120]) if a.startswith('http') else a.replace('/','_')+'.'+kind)
  if p.exists():continue
  try:
   req=urllib.request.Request(u,headers={'User-Agent':'research-lane-fetch/1.0'})
   with urllib.request.urlopen(req,timeout=25) as r:b=r.read();status=r.status;fin=r.geturl()
   p.write_bytes(b)
   if kind=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=False,timeout=60)
   rec=dict(url=u,final_url=fin,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),file=str(p.relative_to(D)))
  except Exception as e:rec=dict(url=u,error=repr(e)[:300])
  rec['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
  print(json.dumps(rec),flush=True)
  with (D/'sources/receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  time.sleep(1.5)
