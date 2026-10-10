import pathlib,json,urllib.request,urllib.error,hashlib,datetime,subprocess,concurrent.futures
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3';P=S/'primary';P.mkdir(exist_ok=True)
items=[('loop-page.html','https://arxiv.org/abs/2607.07617'),('loop.pdf','https://arxiv.org/pdf/2607.07617'),('cone-page.html','https://arxiv.org/abs/2603.04386'),('cone.pdf','https://arxiv.org/pdf/2603.04386'),('almost.pdf','https://backhauszagi.web.elte.hu/aop1294.pdf'),('growing-page.html','https://arxiv.org/abs/1505.06700'),('growing.pdf','https://arxiv.org/pdf/1505.06700')]
def f(it):
 name,url=it;row=dict(name=name,url=url,captured=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I79-research/1.0'}),timeout=50) as r:
   b=r.read();row.update(status=r.status,headers=dict(r.headers),final_url=r.url)
  (P/name).write_bytes(b);row.update(path=str((P/name).relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if name.endswith('.pdf'):
   o=subprocess.run(['pdftotext','-layout',str(P/name),'-'],capture_output=True);(P/name).with_suffix('.txt').write_bytes(o.stdout);row['extraction']={'code':o.returncode,'stderr':o.stderr.decode(errors='replace'),'sha256':hashlib.sha256(o.stdout).hexdigest()}
 except urllib.error.HTTPError as e:
  b=e.read();(P/(name+'.failed-body')).write_bytes(b);row.update(error=repr(e),status=e.code,headers=dict(e.headers),failed_body=str((P/(name+'.failed-body')).relative_to(R)),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:row['error']=repr(e)
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:rows=list(ex.map(f,items))
(S/'primary-requests-2.json').write_text(json.dumps(rows,indent=2));print(json.dumps([{k:x[k] for k in ('name','status','bytes','error') if k in x} for x in rows],indent=2))
