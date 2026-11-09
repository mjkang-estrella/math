import urllib.request,urllib.error,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent;(L/'evidence').mkdir(exist_ok=True);out=[]
for route in ['hyperbolicpoly/2/','crouzeix/6/','shapesurface/6/','stekloveigen/4/','mappingmetric/6/','sparsedomop/3/','crscv/3/']:
 u='https://aimpl.org/'+route; row={'url':u,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source inspection'}),timeout=25) as r:
   b=r.read(5000000);row.update(status=r.status,final_url=r.url,headers=dict(r.headers));assert len(b)<5000000
  p=L/'evidence'/('-'.join(route.strip('/').split('/'))+'.html');p.write_bytes(b);row.update(file=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),size=len(b),version='public AIM page bytes at retrieval; no immutable revision asserted')
 except Exception as e:
  row.update(error=repr(e));out.append(row);(L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(row)
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:break
  continue
 out.append(row);(L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(u,len(b))
