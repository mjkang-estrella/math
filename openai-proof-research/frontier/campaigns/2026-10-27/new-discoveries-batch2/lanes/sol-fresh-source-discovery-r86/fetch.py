import urllib.request,urllib.error,json,hashlib,datetime,pathlib,subprocess
P=pathlib.Path(__file__).resolve().parent
urls={'eruguz.pdf':'https://pure.eur.nl/ws/portalfiles/portal/153391121/1-s2.0-S0305048324000938-main.pdf','hyman.pdf':'https://arxiv.org/pdf/2603.18243v1','fang.pdf':'https://arxiv.org/pdf/2508.12915v1','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
log=[]
for n,u in urls.items():
 r={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research-source-check/1.0'}),timeout=35) as f:
   b=f.read(16000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/'sources'/n).write_bytes(b)
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/n),str(P/'sources'/(n+'.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 log.append(r);print(n,r.get('status',r.get('error')),flush=True)
(P/'http.json').write_text(json.dumps(log,indent=2))
