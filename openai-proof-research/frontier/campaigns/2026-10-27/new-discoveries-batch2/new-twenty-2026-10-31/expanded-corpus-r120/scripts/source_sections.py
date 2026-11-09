from pathlib import Path
import re,json,hashlib
D=Path(__file__).resolve().parents[1];out={}
for p in sorted((D/'sources').glob('22*.txt')):
 s=p.read_text(); hits=[]
 for m in re.finditer(r'(?i)conjectur|we believe|we expect|small gap|T_\{|concav|Einstein functional',s):
  if any(abs(m.start()-h['offset'])<900 for h in hits):continue
  hits.append({'offset':m.start(),'body':s[max(0,m.start()-600):m.start()+2200]})
 out[p.stem]=hits
(D/'outputs/source-sections.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for k,v in out.items():
 print('\nSOURCE',k)
 for h in v:print(h['body'])
