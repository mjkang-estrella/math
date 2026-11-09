from pathlib import Path
import urllib.request,json,hashlib,datetime
D=Path(__file__).parent;p=D/'source-provenance.json';out=json.loads(p.read_text());u='https://content.ems.press/assets/public/full-texts/serials/owr/4/3/1592/online/10.4171-owr-2007-36.pdf';x={'file':'owr2007-36.pdf','url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(u,timeout=35) as r:b=r.read();x['final_url']=r.url
 (D/x['file']).write_bytes(b);x.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
except Exception as e:x['failure']=str(e)
out.append(x);p.write_text(json.dumps(out,indent=2)+'\n');print(x)
