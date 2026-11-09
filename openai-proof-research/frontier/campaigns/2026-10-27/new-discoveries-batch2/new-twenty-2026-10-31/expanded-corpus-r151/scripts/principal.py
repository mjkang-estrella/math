# For each partition g of n into <=A+B parts compute |X cap down(g)| - |Y cap down(g)|; also try pairs.
import sys,itertools
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth import parts_count, combine, dom
from smyth_fast import allparts, pad
A,a,B,b=map(int,sys.argv[1:5]); m=A+B; n=a+b
X={pad(p,m):v for p,v in combine(parts_count(b,A),parts_count(a,B)).items()}
Y={pad(p,m):v for p,v in combine(parts_count(a,A),parts_count(b,B)).items()}
P=list(allparts(n,m))
best=[]
for g in P:
    dx=sum(v for p,v in X.items() if dom(g,p)); dy=sum(v for q,v in Y.items() if dom(g,q))
    best.append((dx-dy,g,dx,dy))
best.sort(reverse=True)
print('top principal deficits',best[:8])
