from pathlib import Path
import urllib.request,json,hashlib,datetime,re
b=Path(__file__).resolve().parent;d=json.loads((b/'live/omega-compare.json').read_text());head=d['commits'][-1]['sha'];results=[]
# Actual four changed bodies, pinned to current head, not an old branch alias.
for i,f in enumerate(d['files']):
 url='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+f['filename'];x={'path':f['filename'],'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as r:data=r.read(3000000);x['status']=r.status
  (b/'live'/f'delta-body-{i}.txt').write_bytes(data);x['sha256']=hashlib.sha256(data).hexdigest();x['target_hits']=[s for s in data.decode().splitlines() if re.search(r'MMPP|Asanjarani|Nazarathy|1905.01736|Markov.modulat|Palm|inter.arrival',s,re.I)]
 except Exception as e:x['error']=str(e)
 results.append(x)
(b/'delta-body-receipts.json').write_text(json.dumps(results,indent=2));print([(x['path'],x.get('status'),x.get('target_hits')) for x in results])
