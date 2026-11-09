import sys,itertools,json
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth import parts_count, combine, dom
from smyth_fast import pad
A,a,B,b=3,20,2,19; m=5
X={pad(p,m):v for p,v in combine(parts_count(b,A),parts_count(a,B)).items()}
Y={pad(p,m):v for p,v in combine(parts_count(a,A),parts_count(b,B)).items()}
G=[tuple(g) for g in json.load(open(sys.argv[1]))['gens']]
G=[pad(g,m) for g in G]
res=[]
for r in range(1,len(G)+1):
    for sub in itertools.combinations(G,r):
        dx=sum(v for p,v in X.items() if any(dom(g,p) for g in sub)); dy=sum(v for q,v in Y.items() if any(dom(g,q) for g in sub))
        if dx>dy: res.append((r,dx-dy,sub,dx,dy))
res.sort()
print('violating subsets',len(res)); 
for x in res[:10]: print(x)
