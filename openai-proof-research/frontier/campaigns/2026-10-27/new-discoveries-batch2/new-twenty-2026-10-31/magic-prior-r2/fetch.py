import requests,pathlib,json,datetime,hashlib,concurrent.futures,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).parent
(p/'sources').mkdir(exist_ok=True);(p/'receipts').mkdir(exist_ok=True)
urls=[('swaminathan.pdf','https://www.sciencedirect.com/science/article/pii/S0012365X06002172/pdf'),('conference.html','https://doi.org/10.1016/s1571-0653(04)00582-7'),('citeseer.pdf','https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=10.1.1.460.4704'),('insa.html','https://insa.nic.in/UI/Archivesection.aspx?JID=MA%3D%3D&JYrs=MjAwMQ%3D%3D'),('springer.pdf','https://link.springer.com/content/pdf/10.1007/s13226-010-0031-z.pdf'),('openai.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('omega-compare.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/b260643d3d496ad9cd04bfc3557fc9b7499de976...HEAD')]
def get(item):
 name,url=item;r={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  x=requests.get(url,timeout=22);(p/'sources'/name).write_bytes(x.content);r.update(status=x.status_code,final_url=x.url,sha256=hashlib.sha256(x.content).hexdigest(),bytes=len(x.content),content_type=x.headers.get('content-type'),redirects=[{'url':y.url,'status':y.status_code} for y in x.history]);print(name,r['status'],r['bytes'])
 except Exception as e:r['error']=str(e);print(name,str(e))
 (p/'receipts'/(name+'.json')).write_text(json.dumps(r,indent=2))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(get,urls))
