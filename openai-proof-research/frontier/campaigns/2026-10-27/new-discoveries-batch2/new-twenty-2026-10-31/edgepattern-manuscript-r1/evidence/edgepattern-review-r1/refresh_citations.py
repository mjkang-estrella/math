from pathlib import Path
import urllib.request,json,datetime,hashlib
out=Path(__file__).resolve().parent/'live';url='https://api.openalex.org/works?filter=cites:W3215181870&per-page=100';r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathDB-independent-review/1.0'}),timeout=25) as f:data=f.read(5000000);r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest());(out/'citations.json').write_bytes(data)
 d=json.loads(data);print('count',d['meta']['count']);print('\n'.join(x['title'] for x in d['results']))
except Exception as e:r['error']=str(e)
(out/'citations.receipt.json').write_text(json.dumps(r,indent=2));print(r)
