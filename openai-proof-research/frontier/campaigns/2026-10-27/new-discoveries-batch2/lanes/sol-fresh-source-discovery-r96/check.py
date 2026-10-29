from pathlib import Path
import json
P=Path(__file__).resolve().parent
Z=(0,); O=(1,); X=(0,1); T=(1,1)
def trim(p):
 p=list(p)
 while len(p)>1 and p[-1]==0:p.pop()
 return tuple(p)
def add(*ps):return trim([sum(p[i] if i<len(p) else 0 for p in ps) for i in range(max(map(len,ps)))])
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def comp(a,b,op):
 c,d,h=a;e,f,k=b
 if op=='S':return add(mul(c,e),mul(T,mul(h,k))),add(mul(d,add(e,mul(T,k))),mul(add(c,mul(T,h)),f)),add(mul(c,k),mul(h,e),mul(X,mul(h,k)))
 return add(mul(c,add(f,mul(T,k))),mul(add(d,mul(T,h)),e)),add(mul(d,f),mul(T,mul(h,k))),add(mul(d,k),mul(h,f),mul(X,mul(h,k)))
def lc(a):return all(a[j]**2>=a[j-1]*a[j+1] for j in range(1,len(a)-1))
def coeff(a,j):return a[j] if 0<=j<len(a) else 0
def cross(a,b,j):return 2*coeff(a,j)*coeff(b,j)-coeff(a,j-1)*coeff(b,j+1)-coeff(b,j-1)*coeff(a,j+1)
E=(O,Z,O); levels={1:{E:'E'}}; count=0;bad=None;cone=None
for n in range(2,10):
 level={}
 for i in range(1,n//2+1):
  for a,sa in levels[i].items():
   for b,sb in levels[n-i].items():
    for op in ['S','P']:
     g=comp(a,b,op)
     if g in level:continue
     level[g]=f'{op}({sa},{sb})';count+=1
     u=add(g[0],mul(T,g[2]))
     if not lc(u) and bad is None:bad=dict(n=n,expression=level[g],U=u)
     for state in range(3):
      if not lc(g[state]) and cone is None:cone=dict(n=n,expression=level[g],states=g,failure='state not LC',state=state)
     for x,y in [(0,1),(0,2),(1,2)]:
      for j in range(max(len(g[x]),len(g[y]))):
       v=cross(g[x],g[y],j)
       if v<0 and cone is None:cone=dict(n=n,expression=level[g],states=g,pair=[x,y],j=j,cross=v)
 levels[n]=level
 print(n,len(level),flush=True)
report=dict(meaning='bounded diagnostics only; no universal proof',counts={n:len(v) for n,v in levels.items()},source_counterexample=bad,first_state_cone_obstruction=cone)
# Direct original parallel-edge deletion-contraction comparison for every n through30.
f=O;bn=E;identities=0
for n in range(1,31):
 if n>1:
  bn=comp(bn,E,'P');f=add(mul(T,f),(((-1)**(n-1)),))
 assert bn[2]==f
 u=add(bn[0],mul(T,bn[2]))
 identities+=1
report['banana_H_equals_source_f_checks']=identities
(P/'check-results.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
known=[1,2,2,4,6,11,18,33,59]
counts=[]
for n in range(1,10):
 counts.append(len({add(a[0],mul(T,a[2])) for a in levels[n]}))
assert counts==known,(counts,known)
report['distinct_U_counts']=counts
(P/'check-results.json').write_text(json.dumps(report,indent=2))
