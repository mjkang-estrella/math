import json,re,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
P=re.compile(rb'2607[.]05941|Hongyu.{0,8}Jia|Zhankui.{0,8}Xiao|zero.{0,12}Jordan.{0,12}product|zero.{0,10}product.{0,10}determined|zJpd|2407[.]00892|(?<![0-9])106693(?![0-9])',re.I)
rows=[]
for j in json.loads((L/'history-matches.json').read_text()):
 b=(R/j['path']).read_bytes(); matches=list(P.finditer(b));row=dict(path=j['path'],sha256=hashlib.sha256(b).hexdigest(),matches=[b[max(0,m.start()-300):m.end()+500].decode(errors='replace') for m in matches]);rows.append(row)
 if matches:print(row)
(L/'original-reopen.json').write_text(json.dumps(rows,indent=2)+'\n')
for name in ['omega','openai']:
 j=json.loads((L/'sources'/f'{name}-head.json').read_text());print(name,j.get('sha'),j.get('commit',{}).get('committer',{}).get('date'))
