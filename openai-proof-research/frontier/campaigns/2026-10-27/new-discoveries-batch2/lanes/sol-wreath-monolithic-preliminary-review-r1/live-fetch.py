import pathlib,urllib.request,datetime,hashlib,json,concurrent.futures
O=pathlib.Path(__file__).resolve().parent; (O/'live').mkdir(exist_ok=True)
items=[('source.pdf','https://arxiv.org/pdf/2602.19340v2'),('abs.html','https://arxiv.org/abs/2602.19340'),('author.html','https://tyleemath.github.io/'),('omega.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/dev'),('main.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/main'),('aim.json','https://api.github.com/repos/MColbrook/AIM/commits/main'),('count.json','https://api.github.com/repos/suvrit/count-ex-machina/git/trees/main'),('openai.json','https://api.github.com/repos/openai/math/commits/main')]
def get(item):
 name,url=item;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'live/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-math-review/1.0'}),timeout=25) as x:
   data=x.read(10000001);assert len(data)<=10000000;r.update(status=x.status,final_url=x.url)
  (O/'live'/name).write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:r['failure']=str(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: rows=list(pool.map(get,items))
(O/'live-http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
