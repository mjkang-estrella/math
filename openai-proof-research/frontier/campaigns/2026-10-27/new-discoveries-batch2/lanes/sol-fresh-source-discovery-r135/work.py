import sys,json,hashlib,urllib.request,datetime,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent
def fetch(name,url):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();r={'url':url,'utc':t,'name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research'}),timeout=40) as f:
   b=f.read(8000001);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),truncated=len(b)>8000000)
  if r['truncated']:raise ValueError('8MB cap')
  (L/'sources'/name).write_bytes(b)
 except Exception as e:r['failure']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r)
if sys.argv[1]=='fetch':
 for name,url in [
 ('hamming.pdf','https://dirros.openscience.si/Dokument.php?id=41814&lang=eng'),
 ('colouring-abs.html','https://arxiv.org/abs/2408.13494'),
 ('colouring.pdf','https://arxiv.org/pdf/2408.13494'),
 ('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),
 ('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD')]:fetch(name,url)
elif sys.argv[1]=='one':fetch(sys.argv[2],sys.argv[3])
