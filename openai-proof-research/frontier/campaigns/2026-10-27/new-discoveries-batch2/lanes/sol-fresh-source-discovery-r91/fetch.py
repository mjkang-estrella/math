import pathlib,urllib.request,json,hashlib,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
jobs={'qwalk.pdf':'https://arxiv.org/pdf/2309.01123v2','general-walk.pdf':'https://arxiv.org/pdf/2601.01542v1','oberwolfach.pdf':'https://publications.mfo.de/bitstream/handle/mfo/4147/OWR_2023_58.pdf?isAllowed=y&sequence=6','mle.pdf':'https://d-nb.info/1303792095/34','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
r=[]
for name,url in jobs.items():
 x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(12000000);x.update(status=f.status,final_url=f.url)
  p=L/'sources'/name;p.write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
