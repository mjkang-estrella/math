import pathlib,json,urllib.request,hashlib,datetime,subprocess
W=pathlib.Path(__file__).resolve().parent
with (W/'successor-sources.jsonl').open('w') as log:
 for id in ['1910.06958','2501.04953']:
  u='https://arxiv.org/pdf/'+id;r={'url':u,'retrieved_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(u,timeout=15) as f:b=f.read()
   p=W/'sources'/(id+'.pdf');p.write_bytes(b);r.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b));log.write(json.dumps(r)+'\n');log.flush();assert b.startswith(b'%PDF');subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
   t=p.with_suffix('.txt');log.write(json.dumps({'path':str(t),'sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'size':t.stat().st_size,'derived_from':str(p)})+'\n');log.flush();print('OK',id)
  except Exception as e:
   r['failure']=repr(e);log.write(json.dumps(r)+'\n');print(r)
   if getattr(e,'code',0) in [403,429]:break
