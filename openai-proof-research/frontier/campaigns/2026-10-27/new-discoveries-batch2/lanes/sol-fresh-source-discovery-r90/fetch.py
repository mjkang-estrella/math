import pathlib,urllib.request,datetime,json,hashlib,subprocess
b=pathlib.Path(__file__).parent
urls={
'lyon.xml':'https://journals.plos.org/plosone/article/file?id=10.1371/journal.pone.0288601&type=manuscript',
'berg2004.html':'https://arxiv.org/html/math/0411282',
'berg2006.html':'https://arxiv.org/html/math/0609442',
'pedersen2023.html':'https://arxiv.org/html/2309.07234',
'omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/main',
'openai-head.json':'https://api.github.com/repos/openai/math/commits/main'}
r=[]
for name,url in urls.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f: data=f.read(10000000);x.update(status=f.status,final_url=f.url)
  (b/'sources'/name).write_bytes(data);x.update(file='sources/'+name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:x['error']=str(e)
 r.append(x)
(b/'http.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r,indent=2))
