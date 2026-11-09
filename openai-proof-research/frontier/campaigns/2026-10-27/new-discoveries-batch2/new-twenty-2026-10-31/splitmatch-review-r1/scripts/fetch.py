from pathlib import Path
import urllib.request,urllib.error,hashlib,json,sys,datetime
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/splitmatch-review-r1')
name,url=sys.argv[1:];d=L/'downloads'/name;d.mkdir()
r=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent mathematical review (public read-only)'}),timeout=35) as f:
  data=f.read(25000000);r.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'));(d/'raw').write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
  if b"Making sure you're not a bot" in data or b'captcha' in data.lower():r['challenge']=True
except Exception as e:r['error']=str(e)
(d/'receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
