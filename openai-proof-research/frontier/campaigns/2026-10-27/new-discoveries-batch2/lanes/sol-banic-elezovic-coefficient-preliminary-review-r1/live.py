import urllib.request,urllib.error,pathlib,json,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parent;(L/'live').mkdir(exist_ok=True)
urls=[('target','https://arxiv.org/abs/2610.17046'),('author','https://arxiv.org/search/?searchtype=author&query=Elezovic%2C+N&abstracts=show&order=-announced_date_first&size=50'),('title','https://arxiv.org/search/?query=%22Discrete+total+variation+under+the+multinomial%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50')]
rows=[]
for name,url in urls:
 row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=22) as r:
   data=r.read(1500000);row.update(status=r.status,final_url=r.url)
  p=L/'live'/(name+'.html');p.write_bytes(data);p.chmod(0o444)
  row.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  text=re.sub('<[^>]+>',' ',data.decode(errors='replace'));text=re.sub(r'\s+',' ',text)
  (L/'live'/(name+'.txt')).write_text(text)
  if re.search(r'captcha|challenge-platform|access denied|too many requests',text,re.I):row['blocked']='challenge/denial; stop route'
 except Exception as e:row['failure']=repr(e)
 rows.append(row)
(L/'live-access.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
