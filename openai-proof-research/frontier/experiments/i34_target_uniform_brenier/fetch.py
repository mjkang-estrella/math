import pathlib,json,hashlib,datetime,urllib.request,urllib.error,concurrent.futures,re,subprocess
s=pathlib.Path('frontier/sources/i34_target_uniform_brenier');p=s/'literature';p.mkdir(exist_ok=True)
urls=[('lm-current','https://arxiv.org/abs/2411.04908'),('ruan-current','https://arxiv.org/abs/2610.07577'),('wang-current','https://arxiv.org/abs/2610.09640'),('dnwp-current','https://arxiv.org/abs/2404.02855'),('bk-current','https://arxiv.org/abs/2002.02022'),('ford-current','https://arxiv.org/abs/2609.35574'),('merigot-current','https://hal.science/hal-05616391'),('delalande','https://proceedings.mlr.press/v151/delalande22a/delalande22a.pdf'),('altschuler-current','https://arxiv.org/abs/2106.11862'),('mulcahy-current','https://arxiv.org/abs/2609.22595')]
def f(kv):
 k,u=kv;d=dict(url=u,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  r=urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research evidence retrieval'}),timeout=40);b=r.read();d.update(status=r.status,final_url=r.url,headers=dict(r.headers))
 except urllib.error.HTTPError as e:b=e.read();d.update(status=e.code,final_url=e.url,error=str(e))
 except Exception as e:b=b'';d.update(status=None,error=repr(e))
 ext='.pdf' if b.startswith(b'%PDF') else '.html';q=p/(k+ext);q.write_bytes(b);d.update(path=str(q),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 if ext=='.pdf':
  z=q.with_suffix('.txt');a=subprocess.run(['pdftotext','-layout',str(q),str(z)],capture_output=True);d['extraction_returncode']=a.returncode
  if z.exists():d['extraction']=dict(path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size)
 else:d['versions']=re.findall(r'\[v\d+\].{0,180}',b.decode(errors='replace'))
 return d
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:a=list(ex.map(f,urls))
(s/'fresh-retrievals.json').write_text(json.dumps(a,indent=2)+'\n');print(json.dumps([{k:v for k,v in x.items() if k in ['url','status','bytes','versions','error']} for x in a],indent=2))
