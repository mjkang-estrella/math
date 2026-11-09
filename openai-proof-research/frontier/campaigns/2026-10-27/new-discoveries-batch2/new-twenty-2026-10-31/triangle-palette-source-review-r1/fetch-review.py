import urllib.request, urllib.error, json, hashlib, datetime, concurrent.futures
from pathlib import Path
r=Path(__file__).parent
urls={'arxiv-abs':'https://arxiv.org/abs/2407.19050','author':'https://home.agh.edu.pl/~pilsniak/publications.html','openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head':'https://api.github.com/repos/teorth/analysis/commits/HEAD','s2':'https://api.semanticscholar.org/graph/v1/paper/ARXIV:2407.19050?fields=title,year,venue,journal,externalIds,citationCount,citations.title,citations.externalIds'}
# Omega URL replaced below from existing receipt, not guessed.
a=r.parent/'expanded-corpus-r58/sources/omega-head.receipt.json'
urls['omega-head']=json.loads(a.read_text())['url']
def get(pair):
 name,url=pair;d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=25) as q: b=q.read();d.update(status=q.status,final_url=q.url)
 except urllib.error.HTTPError as e:b=e.read();d.update(status=e.code,final_url=e.url)
 except Exception as e:b=b'';d.update(error=repr(e))
 (r/(name+'.body')).write_bytes(b);d.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(r/(name+'.receipt.json')).write_text(json.dumps(d,indent=2));return name,d
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for name,d in pool.map(get,urls.items()):print(name,json.dumps(d))
