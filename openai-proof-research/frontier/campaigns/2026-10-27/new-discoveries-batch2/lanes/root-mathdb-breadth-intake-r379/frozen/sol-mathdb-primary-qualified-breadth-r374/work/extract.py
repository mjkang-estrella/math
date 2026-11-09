from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[1]
for e in json.loads((R/'source-provenance.json').read_text()):
 p=R/'sources'/e['name']
 if not e['usable'] or p.suffix!='.pdf':continue
 assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 out=R/'work'/(p.stem+'.txt')
 subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True)
 print(out.name,out.stat().st_size)
