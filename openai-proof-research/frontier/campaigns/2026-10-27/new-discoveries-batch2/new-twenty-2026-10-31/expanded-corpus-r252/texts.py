from pathlib import Path
import subprocess,json,re
L=Path(__file__).resolve().parent
for p in (L/'http').glob('*.pdf'):
 if p.read_bytes()[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15)
for p in sorted((L/'http').glob('*.txt')):
 lines=p.read_text().splitlines(); print('\nFILE',p.name,len(lines))
 for k,s in enumerate(lines):
  if re.search('Conjecture|conjecture|Theorem 1|Theorem 2',s): print(k+1,' '.join(lines[max(0,k-1):k+4]))
