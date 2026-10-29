import functools,json,math
from pathlib import Path

def add(a,b,k=0):
 c=list(a)+[0]*max(0,len(b)+k-len(a))
 for i,x in enumerate(b):c[i+k]+=x
 return tuple(c)
def mul(a,b):
 c=(0,)
 for i,x in enumerate(b):
  if x:c=add(c,tuple(x*y for y in a),i)
 return c
def unimodal(a):
 neg=False
 for x,y in zip(a,a[1:]):
  if y<x:neg=True
  if neg and y>x:return False
 return True

def treecalc(par,delays):
 children={i:[] for i in range(len(par))}
 for i,p in enumerate(par):
  if p>=0:children[p].append(i)
 initial=tuple(range(1,len(par)))
 @functools.lru_cache(None)
 def rec(active,ds):
  if not active:return (1,)
  aset=set(active); leaves=[v for v in active if not any(w in aset for w in children[v])]
  delay=dict(ds);out=(0,)
  for v in leaves:
   if delay[v]!=1:continue
   r=0;w=v
   while par[w]>=0:
    siblings=children[par[w]]; pos=siblings.index(w)
    def size(z):return (1+sum(size(k) for k in children[z])) if z in aset else 0
    r+=sum(size(s) for s in siblings[pos+1:]);w=par[w]
   nxt=tuple(x for x in active if x!=v);ns=set(nxt)
   nl=[x for x in nxt if not any(y in ns for y in children[x])]
   nd=tuple((x,max(1,delay[x]-1) if x in delay else 1) for x in nl)
   out=add(out,rec(nxt,nd),r)
  return out
 return rec(initial,tuple(sorted(delays.items())))
def spider(lengths,ds):
 par=[-1];delay={}
 for l,d in zip(lengths,ds):
  p=0
  for _ in range(l):par.append(p);p=len(par)-1
  delay[p]=d
 return par,delay
out={}
# Fixed structural release-time probes, no enumeration of arbitrary trees.
cases=[((1,1,1),(1,1,2)),((4,1,1),(2,1,4)),((1,4,1),(4,1,2)),((1,1,4),(2,1,4)),((3,2,1),(4,1,2)),((1,2,3),(2,1,4)),((2,3,2),(3,1,3)),((4,2,3),(2,1,4)),((3,4,2),(4,1,2)),((2,2,2),(1,1,3)),((3,1,3),(4,1,4)),((1,3,4),(3,1,2))]
out['spider_probes']=[]
for ls,ds in cases:
 p,d=spider(ls,ds);q=treecalc(p,d)
 out['spider_probes'].append(dict(lengths=ls,delays=ds,coefficients=q,unimodal=unimodal(q)))
# unequal recursive summands disprove the star proof's independence shortcut.
p,d=spider((1,2,1),(1,1,2)); q=treecalc(p,d)
out['unequal_tree_example']={'parents':p,'delays':d,'Q':q,'delete_left_Q':treecalc([-1,0,1,0],{2:1,3:1}),'delete_middle_Q':treecalc([-1,0,0,0],{1:1,2:1,3:1})}
# exact finite diagnostics for the elementary two-uniform smoothing lemma.
nchecks=0
for m in range(2,9):
 for support in [(),(0,),(m,),(0,m),tuple(range(m+1)),(0,m//2,m),tuple(range(0,m+1,2))]:
  a=tuple(int(i in support) for i in range(m+1));v=mul(mul(a,(1,)*m),(1,)*(m-1));assert unimodal(v);nchecks+=1
out['smoothing_diagnostics']=nchecks
# periodic Gram n2 and target product at beta=3,4; sign fixed by monicity.
import sympy as s
x=s.symbols('x');M=s.Matrix([[x,0,1,1],[0,x,1,1],[1,1,x,0],[1,1,0,x]])
assert s.expand(M.det()-x*x*(x*x-4))==0
out['local_Gram_determinant']=str(s.factor(M.det()))
Path('checks.json').write_text(json.dumps(out,indent=2));print(json.dumps({'spider_probes':len(cases),'nonunimodal':[c for c in out['spider_probes'] if not c['unimodal']],'smoothing_checks':nchecks,'local_Gram':'PASS'}))
