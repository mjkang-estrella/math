import pathlib,urllib.request,hashlib,json,datetime,time
p=pathlib.Path.cwd();r=json.loads((p/'reservation.json').read_text());log=[]
for row in r['rows']:
 i=row['mathdb_id'];u=row['source_url'];u=u.replace('/abs/','/html/')
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source review'}),timeout=15) as resp:
   b=resp.read();status=resp.status
  (p/'sources'/f'{i}.html').write_bytes(b)
  log.append({'id':i,'url':u,'status':status,'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 except Exception as e:log.append({'id':i,'url':u,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 (p/'outputs/fetch-receipts.json').write_text(json.dumps(log,indent=2));print(i,log[-1],flush=True)
