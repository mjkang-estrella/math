from pathlib import Path
import hashlib,json,subprocess
L=Path(__file__).resolve().parent; records=[]
for p in (L/'sources').glob('*.pdf'):
 h=hashlib.sha256(p.read_bytes()).hexdigest();q=p.with_suffix('.txt')
 r=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True)
 records.append(dict(original=str(p),sha256=h,text=str(q),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest() if q.exists() else None,exit=r.returncode,error=r.stderr))
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
(L/'extraction.json').write_text(json.dumps(records,indent=2));print([(Path(r['original']).name,r['exit']) for r in records])
