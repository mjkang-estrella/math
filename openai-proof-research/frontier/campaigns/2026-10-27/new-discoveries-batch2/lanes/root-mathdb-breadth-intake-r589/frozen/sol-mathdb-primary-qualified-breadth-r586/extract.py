from pathlib import Path
import subprocess,json,hashlib
D=Path(__file__).parent;out=[]
for p in D.glob('*.pdf'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 q=p.with_suffix('.txt');b=q.read_bytes();out.append({'path':str(q),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'from':str(p)})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
