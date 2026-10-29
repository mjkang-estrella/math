import urllib.request,json,pathlib,hashlib,datetime,concurrent.futures
P=pathlib.Path(__file__).parent
urls={'git':'https://arxiv.org/html/2505.01087v2','git_abs':'https://arxiv.org/abs/2505.01087','ikl':'https://arxiv.org/html/2504.17567v1','ikl_abs':'https://arxiv.org/abs/2504.17567','ikl_successor.pdf':'https://jpmather.math.ncsu.edu/documents/iklpmud.pdf','omega_head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai_head.json':'https://api.github.com/repos/openai/math/commits/HEAD','git_vor':'https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/plms.70096'}
def fetch(item):
 n,u=item
 try:
  r=urllib.request.urlopen(u,timeout=40);b=r.read(); f='sources/'+n; (P/f).write_bytes(b);return dict(name=n,url=u,status=r.status,file=f,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 except Exception as e:return dict(name=n,url=u,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as e: out=list(e.map(fetch,urls.items()))
(P/'http.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
from bs4 import BeautifulSoup
for n in ['git','ikl']:
 (P/'sources'/ (n+'.txt')).write_text(BeautifulSoup((P/'sources'/n).read_bytes(),'html.parser').get_text(' ',strip=True))
