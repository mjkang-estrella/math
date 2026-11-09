import urllib.request,pathlib,json,hashlib,datetime,sys
L=pathlib.Path.cwd(); receipts=[]
rows=json.loads((L/'reservation.json').read_text())['rows']
for r in rows:
 if sys.argv[1:] and str(r['mathdb_id']) not in sys.argv[1:]:continue
 i=r['mathdb_id']; a=r['source_url'].split('/')[-1]; url='https://arxiv.org/html/'+a
 try:
  with urllib.request.urlopen(url,timeout=12) as f: b=f.read(); status=f.status; final=f.url
  (L/f'sources/{i}.html').write_bytes(b)
  receipts.append(dict(id=i,url=url,final=final,status=status,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:receipts.append(dict(id=i,url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 print(receipts[-1],flush=True)
(L/('outputs/fetch-'+('-'.join(sys.argv[1:]) or 'all')+'.json')).write_text(json.dumps(receipts,indent=2))
