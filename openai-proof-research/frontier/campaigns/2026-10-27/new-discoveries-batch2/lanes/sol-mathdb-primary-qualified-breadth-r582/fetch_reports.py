from pathlib import Path
import urllib.request,json,hashlib,datetime
D=Path(__file__).parent;out=json.loads((D/'source-provenance.json').read_text())
for name,url in [('owr736.pdf','https://content.ems.press/assets/public/full-texts/serials/owr/1/3/736/online/10.4171-owr-2004-34.pdf'),('owr711.pdf','https://content.ems.press/assets/public/full-texts/serials/owr/1/1/711/online/10.4171-owr-2004-01.pdf')]:
 x={'file':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();x.update(status=r.status,final_url=r.url)
  (D/name).write_bytes(b);x.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:x['error']=str(e)
 out.append(x)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out[-2:],indent=2))
