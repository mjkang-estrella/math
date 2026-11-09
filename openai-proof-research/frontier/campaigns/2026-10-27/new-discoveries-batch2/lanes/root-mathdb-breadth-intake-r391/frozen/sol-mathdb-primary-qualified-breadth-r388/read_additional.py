from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parent
for e in json.loads((R/'additional-provenance.json').read_text()):
 if 'path' not in e:continue
 p=R/e['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 if p.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
