import pathlib,urllib.request,urllib.error,json,hashlib,datetime
L=pathlib.Path(__file__).parent;D=L/'primary';D.mkdir(exist_ok=True)
for name,url in [('solynin','https://www.mathnet.ru/links/19412beb4bd62c2ca09d88bcd5a11da0/sm361_eng.pdf'),('stories','https://arxiv.org/pdf/1801.01692v1'),('integrable','https://arxiv.org/pdf/1804.03737v1')]:
 m={'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'original_source_body' if name!='egres' else 'individual_original_problem_page','version':'1809.07200v1' if name=='hayman' else 'unversioned; exact bytes pinned'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source inspection'}),timeout=35) as r:
   b=r.read(12000000);assert len(b)<12000000;m.update(status=r.status,final_url=r.url,headers=dict(r.headers),size=len(b),sha256=hashlib.sha256(b).hexdigest())
  ext='pdf' if b.startswith(b'%PDF') else 'html';p=D/(name+'.'+ext);p.write_bytes(b);m['file']=p.name
 except Exception as e:m['failure']=str(e);m['retry']=False
 (D/(name+'.meta.json')).write_text(json.dumps(m,indent=2)+'\n');print(name,m.get('status'),m.get('size'),m.get('failure'))
