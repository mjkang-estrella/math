from pathlib import Path
import json,hashlib,subprocess
L=Path(__file__).parent
for r in json.loads((L/'sources.json').read_text()):
 if r.get('status')!=200 or r.get('challenge') or not r.get('path','').endswith('.pdf'):continue
 p=Path(r['path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'] and len(b)==r['size']
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 print(p.name,p.with_suffix('.txt').stat().st_size)
