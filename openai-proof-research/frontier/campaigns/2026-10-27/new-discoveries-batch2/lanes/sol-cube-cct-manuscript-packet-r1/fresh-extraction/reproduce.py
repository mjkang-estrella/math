from itertools import product
import json
Z=[2,9,10,13,19,20];X=set(Z)-{9};Y=set(Z)-{2}
p=[tuple(-1 if v>>i&1 else 1 for i in range(5)) for v in range(32)]
fibers={}
for u,v in product(p,repeat=2):
 s=tuple(a+b for a,b in zip(u,v));fibers[s]=fibers.get(s,0)+1
w=lambda x,y:fibers[tuple(a+b for a,b in zip(p[x],p[y]))]
table=[[w(x,y) for y in Z] for x in Z];scores=list(map(sum,table))
assert scores==[39,39,39,51,45,57] and scores.count(51)==1
g=lambda v:1^sum(((v>>i)&1)<<j for i,j in enumerate([0,3,4,2,1]))
assert {g(v) for v in X}==Y and w(9,13)==2 and w(2,13)==16
print(json.dumps({'Z':Z,'table':table,'scores':scores,'map_X':{v:g(v) for v in sorted(X)},'contradiction':[2,16]},indent=2))
