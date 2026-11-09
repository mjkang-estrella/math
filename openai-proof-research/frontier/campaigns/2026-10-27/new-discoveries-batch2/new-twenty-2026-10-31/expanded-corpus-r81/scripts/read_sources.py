from pathlib import Path

import json,re
D=Path(__file__).resolve().parents[1]
import textify
x=json.loads((D/'extracted.json').read_text()); out=[]
for i,o in x.items():
 if '/abs/' not in o['source_url']:continue
 p=D/'sources'/(o['source_url'].split('/abs/')[1].replace('/','_')+'.txt')
 if not p.exists():continue
 t=p.read_text();out.append(f'\n### {i} {o["title"]}\n')
 # All conjecture neighborhoods, with byte offsets to full extracted text.
 for m in list(re.finditer(r'conjectur',t,re.I))[:35]:out.append(f'offset {m.start()}: '+t[max(0,m.start()-160):m.start()+1050]+'\n')
(D/'outputs/source-excerpts.txt').write_text('\n'.join(out))
for key in ['openai-head','omega-head']:
 o=json.loads((D/'sources'/f'{key}.json').read_text());print(key,o['sha'])
