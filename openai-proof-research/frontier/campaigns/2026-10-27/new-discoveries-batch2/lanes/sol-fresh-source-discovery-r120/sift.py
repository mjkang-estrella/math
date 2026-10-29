import json,re,hashlib,shutil
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parent.parent
reports=[];specific=[]
for line in (L/'target-matches.jsonl').open():
 r=json.loads(line);p=r['path'];name=Path(p).name
 if any(s in p for s in ['history-index','history-audit','inventory','.venv/','site-packages/']):continue
 if re.search(r'(SUMMARY|discovery|review|EXCLUSION|DECISION|disposition|FINDINGS|STATUS)',name,re.I):reports.append(r)
 if any(re.search(r'Nielsen.{0,30}(beta|β)|1805[.]01462|jca-27-09',x['text'],re.I) for x in r['matches']):specific.append(r)
(L/'relevant-history.json').write_text(json.dumps({'reports':reports,'specific':specific},indent=2)+'\n')
print('Reports:',len(reports))
for r in reports:print(r['path'])
print('Specific bodies:',len(specific))
for r in specific:print(r['path'])
