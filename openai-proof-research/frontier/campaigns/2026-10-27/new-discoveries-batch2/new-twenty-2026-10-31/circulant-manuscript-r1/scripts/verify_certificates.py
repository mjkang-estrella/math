"""Independent modular classification and positive-witness verification. No writes."""
from pathlib import Path
import json,itertools
W=Path(__file__).resolve().parents[1]
counts={'triangle':0,'distance_obstruction':0,'residual':0}
res=[]
for m in range(128):
 S={v%15 for d in range(1,8) if m>>(d-1)&1 for v in [d,-d]}
 if any((b-a)%15 in S for a in S for b in S):label='triangle'
 elif len({0}|S|{(a+b)%15 for a in S for b in S})<15:label='distance_obstruction'
 else:label='residual';res.append(m)
 counts[label]+=1
 row=json.loads((W/'evidence/classification.json').read_text())['rows'][m]
 assert row['mask']==m and row['label']==label
assert counts=={'triangle':109,'distance_obstruction':17,'residual':2} and res==[41,70]
rows=json.loads((W/'evidence/coverage-verified.json').read_text())
assert [r['n'] for r in rows]==list(range(11,41))
for row in rows:
 n=row['n']
 if n==15:assert not row['exists'];continue
 assert row['exists'];r=row['certificate'];assert r['n']==n
 S={x%n for d in r['positive_jumps'] for x in [d,-d]};covered=set()
 for p in r['witnesses'].values():
  assert len(p)==len(set(p)) and all(0<=v<n for v in p)
  assert all((((b-a)%n in S)==(j==i+1)) for i,a in enumerate(p) for j,b in enumerate(p) if i<j)
  for delta in range(n):
   for t in itertools.combinations(p,3):covered.add(tuple(sorted((x+delta)%n for x in t)))
 assert len(covered)==n*(n-1)*(n-2)//6
 assert len({0}|S|{(a+b)%n for a in S for b in S})==n and len(S)<n-1
print('PASS: 128 masks (109/17/2); all triple-path witnesses at 29 orders in 11..40 except 15')
