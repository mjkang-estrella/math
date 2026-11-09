from pathlib import Path
import subprocess,json,hashlib,re
L=Path(__file__).resolve().parents[1]
for p in (L/'sources').glob('*.pdf'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
for p in (L/'sources').glob('*.abs.html'):
 s=p.read_text();print(p.name, re.findall(r'\[v\d+\].{0,180}',s))
