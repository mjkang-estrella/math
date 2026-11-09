from pathlib import Path
import json,hashlib,urllib.request,datetime
from html.parser import HTMLParser
D=Path(__file__).resolve().parent;p=D/'model.html';url='https://www-users.cse.umn.edu/~tlawson/hovey/model.html'
pv=json.loads((D/'source-provenance.json').read_text());r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=20) as f:b=f.read();r.update(final_url=f.url,status=f.status)
 p.write_bytes(b);r.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest());pv.append(r);(D/'source-provenance.json').write_text(json.dumps(pv,indent=2)+'\n')
 class H(HTMLParser):
  def handle_data(self,x):self.t.append(x)
 h=H();h.t=[];h.feed(b.decode());p=p.with_suffix('.txt');p.write_text(''.join(h.t));der=json.loads((D/'derivative-bindings.json').read_text());der.append({'path':str(p),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'from':r['path']});(D/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
except Exception as e:r['failure']=str(e);pv.append(r);(D/'source-provenance.json').write_text(json.dumps(pv,indent=2)+'\n')
print(r)
