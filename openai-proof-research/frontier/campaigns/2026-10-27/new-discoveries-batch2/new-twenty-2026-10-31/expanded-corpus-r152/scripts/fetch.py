import pathlib,json,urllib.request,hashlib,datetime,time
L=pathlib.Path(__file__).resolve().parents[1]; rows=json.loads((L/'reservation.json').read_text())['rows']; receipts=[]
for r in rows:
 i=r['mathdb_id']; a=r['source_url'].rsplit('/',1)[1]
 for kind,url in [('abs',r['source_url']),('pdf','https://arxiv.org/pdf/'+a)]:
  dest=L/f'sources/{i}.{kind}'
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=12) as h: data=h.read(); status=h.status; final=h.url
   dest.write_bytes(data); rec={'id':i,'url':url,'final_url':final,'status':status,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
  except Exception as e: rec={'id':i,'url':url,'error':str(e)}
  rec['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat(); receipts.append(rec); print(json.dumps(rec),flush=True)
  (L/'outputs/http-receipts.json').write_text(json.dumps(receipts,indent=2))
