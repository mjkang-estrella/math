from pathlib import Path
import json,re,hashlib
L=Path(__file__).parent;out=[]
for p in sorted((L/'sources').glob('*.txt')):
 s=p.read_text(); lines=s.splitlines();hits=[i for i,l in enumerate(lines) if re.search(r'conjecture|open problem|question [0-9]',l,re.I)]
 print('\nSOURCE',p.stem, 'HEADER',' '.join(lines[:6]))
 for i in hits:print(i+1,lines[i][:220])
 out.append({'file':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'conjecture_line_locators':[i+1 for i in hits],'read_status':'locators only; not proof audits'})
(L/'locators.json').write_text(json.dumps(out,indent=2)+'\n')
