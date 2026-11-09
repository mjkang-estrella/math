import json,pathlib,urllib.request,datetime,hashlib,concurrent.futures,subprocess
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
ids=sorted({e['record']['source_url'].rsplit('/',1)[-1] for e in json.loads((L/'assigned-records.json').read_text())})
def get(i):
 u='https://arxiv.org/pdf/'+i;e={'url':u,'requested_version':'unversioned arXiv PDF endpoint; version must be read from PDF','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'arxiv_id':i}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research screening source audit'}),timeout=15) as f:
   b=f.read(10*1024*1024+1);e.update(status=f.status,final_url=f.url)
  assert len(b)<=10*1024*1024,'size cap';assert b.startswith(b'%PDF'),'non-PDF response'
  p=L/'sources'/(i+'.pdf');p.write_bytes(b);e.update(path=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  t=p.with_suffix('.txt');r=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True);e['pdftotext_exit']=r.returncode
  if t.exists():e['text_sha256']=hashlib.sha256(t.read_bytes()).hexdigest()
 except Exception as x:e['failure']=str(x)
 return e
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
 out=list(ex.map(get,ids))
(L/'retained-sources.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:print(json.dumps(e))
