from pathlib import Path
import json,subprocess,re,hashlib,html
L=Path(__file__).resolve().parent
for e in json.loads((L/'source-provenance.json').read_text()):
 if 'sha256' not in e:continue
 p=L/e['file']; assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 if p.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 else:
  s=p.read_text();p.with_suffix('.txt').write_text(html.unescape(re.sub('<[^>]+>',' ',s)))
