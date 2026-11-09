from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[1]
for e in json.loads((R/'source-provenance.json').read_text()):
 if e.get('usable') and e['path'].endswith('.pdf'):
  p=R/e['path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'];subprocess.run(['pdftotext','-layout',str(p),str(R/'work'/(e['key']+'.txt'))],check=True)
