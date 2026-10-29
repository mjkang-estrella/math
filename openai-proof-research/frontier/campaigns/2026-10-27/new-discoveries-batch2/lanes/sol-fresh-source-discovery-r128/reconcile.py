from research import *
from collections import defaultdict
D=defaultdict(list)
for l in (H/'focused-matches.jsonl').open():
 x=json.loads(l);D[x['path']].append(x)
for p,xs in D.items():
 print(p,len(xs),' | '.join(x['excerpt'][max(0,x['excerpt'].find('Cavey')-30):][:180].replace('\n',' ') for x in xs[:2]))
save('original-hit-receipts.json',[{'path':p,'sha256':xs[0]['sha256'],'matches':len(xs)} for p,xs in D.items()])
