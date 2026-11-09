import pathlib,json,urllib.request,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((D/'reservation.json').read_text())['rows']; receipt=[]
for r in rows:
 a=r['source_url'].split('/')[-1]
 for kind,url in [('abs',r['source_url']),('pdf','https://arxiv.org/pdf/'+a)]:
  p=D/'sources'/f'{a}.{kind}'
  if p.exists():continue
  o={'id':r['mathdb_id'],'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review/1.0'}),timeout=15) as f:b=f.read();o['status']=f.status
   p.write_bytes(b);o.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
   if kind=='pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=12,capture_output=True)
  except Exception as e:o['error']=str(e)
  receipt.append(o); (D/'sources/receipts.json').write_text(json.dumps(receipt,indent=2)+'\n')
  print(o,flush=True)
