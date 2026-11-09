#!/usr/bin/env python3
from pathlib import Path
import json,re
D=Path(__file__).resolve().parents[1]
s=(D/'formal/Cube.lean').read_text() if (D/'formal').exists() else (D/'gate1-extracted/formal/Cube.lean').read_text()
A=list(map(int,re.search(r'\(\[(.*?)\]\.map vertex',s,re.S)[1].replace('\n','').split(',')))
def digits(k):return [(k//2**i)%2 for i in range(8)]
def d(x,y):return sum(a!=b for a,b in zip(digits(x),digits(y)))
assert len(set(A))==len(A)==34
hist=[sum(d(x,y)==i for x in A for y in A) for i in range(9)]
assert hist==[34,72,276,308,276,190,0,0,0]
rows=[]
for x in range(256):
 m=max(d(x,y) for y in A);y=next(y for y in A if d(x,y)==m)
 assert m==5 if x in A else m>5
 rows.append(dict(vertex=x,in_A=x in A,maximum=m,partner=y))
(D/'independent-certificate.json').write_text(json.dumps(dict(A=A,ordered_distance_counts=hist,rows=rows),indent=2)+'\n')
print('PASS: 1156 ordered pairs; 34 members; 222 outsiders; coordinate comparison, no author checker imported')
