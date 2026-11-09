from pathlib import Path
import json,hashlib,urllib.request,subprocess,datetime
O=Path(__file__).parent;refs=json.loads((O/'flat-bindings.json').read_text())
def bind(p):
 b=p.read_bytes();refs.append({'path':str(p.resolve()),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()});(O/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for n in ['PROOF.md','PRIOR_METHOD.md','provenance.json']:
 bind(O.parent/'astra-algebra-matrix-r2'/n)
p=O/'sources/2201.04554.pdf';url='https://arxiv.org/pdf/2201.04554'
try:
 with urllib.request.urlopen(url,timeout=15) as r:
  b=r.read();headers=dict(r.headers);assert b.startswith(b'%PDF');p.write_bytes(b)
 bind(p);t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);bind(t)
 (O/'successor-provenance.json').write_text(json.dumps({'url':url,'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':headers,'bound_before_reading':True},indent=2)+'\n')
except Exception as e:(O/'successor-failure.json').write_text(json.dumps({'url':url,'error':repr(e),'no_retry':True})+'\n')
