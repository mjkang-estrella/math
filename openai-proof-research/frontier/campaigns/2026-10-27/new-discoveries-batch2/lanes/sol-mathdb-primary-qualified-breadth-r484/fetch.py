import pathlib,json,urllib.request,hashlib,subprocess,datetime
W=pathlib.Path(__file__).resolve().parent;(W/'sources').mkdir(exist_ok=True)
a=json.loads((W/'assigned-records.json').read_text()); urls=list(dict.fromkeys(r['record']['source_url'].replace('/abs/','/pdf/') for r in a));urls.sort(key=lambda u:(not any(s in u for s in ['1911.03707','1907.08608','1908.05220','1909.03693','1910.06442','1907.08049','1907.10962','1910.07349']),u))
with (W/'sources.jsonl').open('w') as log:
 for u in urls:
  r={'url':u,'retrieved_at':datetime.datetime.now(datetime.timezone.utc).isoformat()};p=W/'sources'/(u.rsplit('/',1)[1]+'.pdf')
  try:
   with urllib.request.urlopen(u,timeout=15) as f:b=f.read();r['final_url']=f.url
   p.write_bytes(b);r.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b));log.write(json.dumps(r)+'\n');log.flush()
   if not b.startswith(b'%PDF'):r['failure']='non-PDF retained';print(r);break
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
   print('OK',u,len(b),flush=True)
  except Exception as e:
   r['failure']=repr(e);log.write(json.dumps(r)+'\n');log.flush();print(r,flush=True)
   if getattr(e,'code',0) in [403,429]:break
