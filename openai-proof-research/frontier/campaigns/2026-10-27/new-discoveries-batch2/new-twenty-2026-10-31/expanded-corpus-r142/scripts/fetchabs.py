import urllib.request,pathlib,json,hashlib,datetime,sys,time
L=pathlib.Path.cwd(); receipts=[]
rows=json.loads((L/'reservation.json').read_text())['rows']
kind=sys.argv[1]  # abs or html
ids=sys.argv[2:]
for r in rows:
 if ids and str(r['mathdb_id']) not in ids:continue
 i=r['mathdb_id']; a=r['source_url'].split('/')[-1]; url=f'https://arxiv.org/{kind}/'+a
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'research-lane-fetch/1.0'})
  with urllib.request.urlopen(req,timeout=20) as f: b=f.read(); status=f.status; final=f.url
  (L/f'sources/{i}.{kind}.html').write_bytes(b)
  receipts.append(dict(id=i,url=url,final=final,status=status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:receipts.append(dict(id=i,url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 print(receipts[-1],flush=True); time.sleep(1.5)
(L/('outputs/fetch-'+kind+'-'+('-'.join(ids) or 'all')+'.json')).write_text(json.dumps(receipts,indent=2))
