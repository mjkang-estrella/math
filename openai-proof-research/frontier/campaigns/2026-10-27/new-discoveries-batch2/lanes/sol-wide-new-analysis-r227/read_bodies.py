from retrieve import *
refs=[]
for p in (L/'primary').glob('*.txt'):
 refs.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(L/'text-freeze.json').write_text(json.dumps(refs,indent=2))
for r in refs:
 p=pathlib.Path(r['path']);s=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 print('\nBODY',p.name,'\n',s[:1400])
 if '1905.01736' in p.name: print(s);continue
 import re
 locs=[m.start() for m in re.finditer(r'(?i)(?:open problem|conjecture|question|problem\s+\d)',s)]
 for j in locs[:16]:print(s[max(0,j-250):j+1600])
