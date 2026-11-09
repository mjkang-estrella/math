import pathlib,urllib.request,hashlib,json,datetime,concurrent.futures
out=pathlib.Path(__file__).resolve().parent
urls={'torus':'https://arxiv.org/pdf/1203.6604','determinant':'https://arxiv.org/pdf/1203.6812','deviation':'https://arxiv.org/pdf/1205.3121','palomar-torus':'https://data.palomar-registry.org/api/v1/results?q=no-three-in-line','palomar-deviation':'https://data.palomar-registry.org/api/v1/results?q=deviation','palomar-determinant':'https://data.palomar-registry.org/api/v1/results?q=diagonally+balanced'}
def fetch(pair):
 k,u=pair;r={'name':k,'url':u,'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=45) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  p=out/(k+('.pdf' if k in ['torus','determinant','deviation'] else '.body'));p.write_bytes(b);r.update(file=p.name,sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['error']=str(e)
 return r
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:r=list(pool.map(fetch,urls.items()))
 (out/'source-receipts.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
