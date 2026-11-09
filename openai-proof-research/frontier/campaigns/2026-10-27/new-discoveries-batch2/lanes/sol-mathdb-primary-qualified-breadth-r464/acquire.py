import json,pathlib,urllib.request,urllib.error,hashlib,datetime,subprocess,concurrent.futures
L=pathlib.Path(__file__).resolve().parent; (L/'sources').mkdir(exist_ok=True)
rs=json.loads((L/'records.json').read_text()); urls=sorted({x['record']['source_url'] for x in rs})
def job(u):
 aid=u.split('/abs/')[-1]; url='https://arxiv.org/pdf/'+aid; p=L/'sources'/(aid+'.pdf'); r={'url':url,'version':'current arXiv PDF; version stamp in retained body','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'ids':[x['record']['mathdb_id'] for x in rs if x['record']['source_url']==u]}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=20) as f:
   data=f.read(16000000); r['final_url']=f.url; r['status']=f.status; (p.with_suffix('.headers')).write_text(str(f.headers))
  p.write_bytes(data); r.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  assert data.startswith(b'%PDF'), 'not PDF; stop, no retry'
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=12)
  r['text_path']=str(p.with_suffix('.txt')); r['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as e: r['failure']=str(e); r['access']='HOLD; no retry or alternative route'
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex: out=list(ex.map(job,urls))
(L/'sources.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'sources':len(out),'success':sum('text_path' in x for x in out),'failures':[x for x in out if 'failure' in x]},indent=2))
