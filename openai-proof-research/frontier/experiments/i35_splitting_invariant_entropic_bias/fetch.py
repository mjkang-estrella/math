import pathlib,json,hashlib,urllib.request,urllib.error,concurrent.futures,datetime
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i35_splitting_invariant_entropic_bias';D=S/'literature';D.mkdir(exist_ok=True)
requests=[('dnwp','https://arxiv.org/abs/2404.02855'),('delalande','https://arxiv.org/abs/2110.12678'),('altschuler','https://arxiv.org/abs/2106.11862'),('lm','https://arxiv.org/abs/2411.04908'),('ruan','https://arxiv.org/abs/2610.07577'),('wang','https://arxiv.org/abs/2610.09640'),('merigot','https://hal.science/hal-05616391v1'),('bk','https://arxiv.org/abs/2002.02022'),('ford','https://arxiv.org/abs/2609.35574')]
def get(z):
 name,url=z;t=datetime.datetime.now(datetime.timezone.utc).isoformat();err=None
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I35 mathematical research source verification'}),timeout=35) as r: b=r.read();status=r.status;final=r.url;headers=dict(r.headers)
 except urllib.error.HTTPError as e:b=e.read();status=e.code;final=e.url;headers=dict(e.headers);err=str(e)
 except Exception as e:b=str(e).encode();status=None;final=url;headers={};err=str(e)
 p=D/(name+'-current.html');p.write_bytes(b)
 return dict(request_url=url,final_url=final,retrieved_utc=t,status=status,error=err,headers=headers,path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: rows=list(pool.map(get,requests))
(S/'fresh-retrievals.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps([{k:r[k] for k in ['request_url','status','bytes','error']} for r in rows],indent=2))
