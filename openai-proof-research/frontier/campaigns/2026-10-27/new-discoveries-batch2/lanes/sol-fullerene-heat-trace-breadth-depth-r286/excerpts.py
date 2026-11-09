from pathlib import Path
import re,json,sys,runpy
L=Path(__file__).resolve().parent;sys.argv=['work','freeze',str(L/'exact-signs.json')];ns=runpy.run_path(str(L/'work.py'));freeze=ns['freeze']
for p in sorted((L/'primary').glob('*.txt')):
 if not re.match(r'\d',p.name) or p.name[:4] not in ['2404','2406','2407','2408','2411']:continue
 s=freeze(p).read_text();lines=s.splitlines();print('\nSOURCE',p.name,' '.join(lines[:10]))
 pat=r'^\s*(Conjecture|Question|Problem|Open problem)\s*\d|^\s*Open Problem|^\s*Conjecture\.|\bTheorem 1.1\b|\bOpen question\b'
 hits=[i for i,x in enumerate(lines) if re.search(pat,x,re.I)]
 if p.name.startswith('1910'):hits=[418,439,450]
 for i in hits[:3]:print('\n'.join(f'{j+1}: {lines[j][:220]}' for j in range(i,min(len(lines),i+16))))
