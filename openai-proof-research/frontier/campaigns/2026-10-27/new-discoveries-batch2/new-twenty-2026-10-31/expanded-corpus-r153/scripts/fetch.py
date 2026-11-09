import pathlib,json,urllib.request,datetime,hashlib,sys
L=pathlib.Path(__file__).resolve().parents[1]; rows=json.loads((L/'reservation.json').read_text())['rows']; receipts=[]
for r in rows:
 if len(sys.argv)>1 and str(r['mathdb_id']) not in sys.argv[1:]:continue
 u=r['source_url']; a=u.split('/')[-1]
 urls=[('abs',u),('pdf','https://arxiv.org/pdf/'+a)] if 'arxiv' in u else [('abs',u)]
 for kind,url in urls:
  dest=L/'sources'/f"{r['mathdb_id']}.{kind}"
  rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(dest)}
  try:
   with urllib.request.urlopen(url,timeout=18) as f: data=f.read();rec.update(status=f.status,final_url=f.url)
   dest.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  except Exception as e:rec['error']=str(e)
  receipts.append(rec); print(json.dumps(rec),flush=True)
 with (L/'outputs/http.jsonl').open('a') as f:
  for x in receipts:f.write(json.dumps(x)+'\n')
 receipts=[]
