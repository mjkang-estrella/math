import urllib.request,json,datetime,re,hashlib
from pathlib import Path
out=[]
for org,repo in [('the-omega-institute','trureturing'),('openai','math')]:
 url=f'https://github.com/{org}/{repo}'
 r={'url':url,'attempted_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read(8000000);r['http_status']=f.status
  p=Path('sources')/(repo+'-current-page.html');p.write_bytes(data)
  r['sha256']=hashlib.sha256(data).hexdigest()
  r['currentOid_matches']=sorted(set(re.findall(rb'"currentOid":"([0-9a-f]{40})"',data)))
  r['currentOid_matches']=[x.decode() for x in r['currentOid_matches']]
 except Exception as e:r['error']=str(e)
 out.append(r)
Path('registry-refresh.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
