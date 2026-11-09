import json,pathlib,sys
from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for name,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing')]:
 h=json.loads((D/f'sources/{name}-head.json').read_text()); print(name,h['sha'],h['commit']['tree']['sha'],flush=True)
 get((name+'-tree.json',f"https://api.github.com/repos/{repo}/git/trees/{h['commit']['tree']['sha']}?recursive=1"))
 t=json.loads((D/f'sources/{name}-tree.json').read_text()); print('truncated',t.get('truncated'))
 ids=json.loads((D/'reservation.json').read_text())['ids']; hits=[x['path'] for x in t.get('tree',[]) if any(str(i) in x['path'] for i in ids)]
 print('id path hits',hits)
