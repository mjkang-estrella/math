from pathlib import Path
import urllib.request,datetime,hashlib,json
out=Path(__file__).resolve().parent/'live';out.mkdir(exist_ok=True)
urls={'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head':'https://api.github.com/repos/leanprover-community/omega/commits/HEAD','arxiv-history':'https://arxiv.org/abs/1904.05618','siam-landing':'https://epubs.siam.org/doi/10.1137/20M1382283'}
# Registry owner read from inherited receipt rather than guessing.
b=out.parent.parent/'edgepattern-formal-r1/prior/omega-head.json.receipt.json'
r=json.loads(b.read_text());print(r)
if 'url' in r:urls['omega-head']=r['url']
for name,url in urls.items():
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathDB-independent-review/1.0'}),timeout=25) as f:
   data=f.read(8000000);receipt.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest());(out/(name+'.body')).write_bytes(data)
 except Exception as e:receipt['error']=str(e)
 (out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
