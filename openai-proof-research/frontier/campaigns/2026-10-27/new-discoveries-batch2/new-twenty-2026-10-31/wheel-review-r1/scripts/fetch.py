from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys
D=Path.cwd()
for name,url in [
 ('openai-head','https://api.github.com/repos/openai/math/commits/HEAD'),
 ('omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),
 ('authors-head','https://api.github.com/repos/Shivaramkratos/Ultimate_Independence_ratio_Python_Gurobi_code/commits/HEAD'),
 ('source-abs','https://arxiv.org/abs/2511.18747'),
 ('source-html','https://arxiv.org/html/2511.18747v1'),
 ('openalex-citations','https://api.openalex.org/works?filter=cites:W7106693227&per-page=100'),
 ('later-wheel-search','https://arxiv.org/search/?query=wheel+fractional&searchtype=all&abstracts=show&order=-announced_date_first&size=50'),
 ('author-search','https://arxiv.org/search/?query=Clow%2C+Alexander&searchtype=author&abstracts=show&order=-announced_date_first&size=50')]:
 if (D/'receipts'/(name+'.json')).exists():continue
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-independent-review/1.0'}),timeout=25) as r:data=r.read();rec.update(status=r.status,final_url=r.url)
  (D/'receipts'/(name+'.body')).write_bytes(data);rec['sha256']=hashlib.sha256(data).hexdigest()
 except Exception as e:rec['error']=str(e)
 (D/'receipts'/(name+'.json')).write_text(json.dumps(rec,indent=2));print(rec,flush=True)
