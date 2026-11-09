from pathlib import Path
import json,re
D=Path(__file__).resolve().parents[1]
def check(n,l):
 es=[(i,(i+1)%(2*n)) for i in range(2*n)]+[(i,i+n) for i in range(n)]
 assert sorted(l)==list(range(1,3*n+1))
 assert len(set(tuple(sorted(e)) for e in es))==3*n
 s=[sum(x for (u,w),x in zip(es,l) if v in (u,w)) for v in range(2*n)]
 assert all(s[u]!=s[v] for u,v in es);assert len(set(s))==3
 cycle=list(range(n+1))+[0];assert (len(cycle)-1)%2==1
 assert all((u,v) in es or (v,u) in es for u,v in zip(cycle,cycle[1:]))
 return dict(n=n,labels=l,sums=s,distinct=sorted(set(s)),proper=True,odd_cycle=cycle)
r=[check(6,[17,13,7,8,3,15,6,18,4,5,12,2,10,1,9,16,14,11]),check(4,[11,2,9,12,5,10,6,8,3,7,4,1])]
for line in (D/'logs/search.log').read_text().splitlines():
 m=re.match(r'n=(\d+) found=1.*labels=(.*)',line)
 if m:r.append(check(int(m[1]),[int(x) for x in m[2].split(',') if x]))
print(json.dumps({'checks':r,'correct_double_total_M8':2*sum(range(1,13)),'printed_total':132},indent=2))
