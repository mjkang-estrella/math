import pathlib,json,urllib.request,datetime,hashlib,importlib.util
L=pathlib.Path(__file__).parent
out=[]
urls=['https://arxiv.org/abs/2104.09241','https://arxiv.org/abs/2608.10012','https://export.arxiv.org/api/query?search_query=all:%22abnormal%20edges%22&max_results=10']
(L/'current').mkdir(exist_ok=True)
for i,u in enumerate(urls):
 r={'url':u,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'bounded-mathematics-research/1.0'}),timeout=20) as f:
   b=f.read(2000001);assert len(b)<=2000000;r.update(status=f.status,final_url=f.url)
  p=L/'current'/f'{i}.html';p.write_bytes(b);r.update(file=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:r['failure']=repr(e)
 out.append(r)
(L/'current-access.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out));print({x:bool(importlib.util.find_spec(x)) for x in ['z3','ortools','scipy','pysat']})
