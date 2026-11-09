import json,pathlib,urllib.request,hashlib,datetime,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((D/'reservation.json').read_text())['rows']
items={x['source_url'].split('/')[-1] for x in rows}|{'2610.22783'}
if len(sys.argv)>1:items=set(sys.argv[1:])
receipts=[]
for a in sorted(items):
 for kind in ['abs','pdf']:
  u=f'https://arxiv.org/{kind}/{a}';p=D/'sources'/f'{a}.{kind}'
  if p.exists():continue
  try:
   with urllib.request.urlopen(u,timeout=15) as r:b=r.read();status=r.status
   p.write_bytes(b)
   if kind=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=False)
   rec=dict(url=u,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),file=str(p))
  except Exception as e:rec=dict(url=u,error=str(e))
  rec['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();receipts.append(rec)
  print(json.dumps(rec),flush=True)
  with (D/'sources/receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
