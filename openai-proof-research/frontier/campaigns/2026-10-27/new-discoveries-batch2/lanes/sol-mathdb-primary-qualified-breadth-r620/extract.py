from pathlib import Path
import json,hashlib,subprocess
P=Path(__file__).parent;out=[]
for d in json.loads((P/'source-provenance.json').read_text()):
 if 'failure' in d:continue
 p=P/(d['name']+'.pdf');b=p.read_bytes();assert len(b)==d['size'] and hashlib.sha256(b).hexdigest()==d['sha256']
 t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes()
 out.append({'path':t.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'parent_sha256':d['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
