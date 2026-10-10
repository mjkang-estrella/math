"""Independent small exhaustive checks and elementary identities. Stdout only."""
import json,sys,runpy
from pathlib import Path
from itertools import product
from math import factorial
ROOT=Path(__file__).resolve().parents[3]
D=runpy.run_path(str(ROOT/'frontier/experiments/i108_galois_tuple_divisibility/tuple_search.py'))

def direct(g,p,t,n):
 tab,inv,orders=g;N=len(tab);cs=[C for C in D['classes'](tab,inv) if orders[next(iter(C))]%p==0];sing=sorted(set().union(*cs));counts={}
 def power(x,a):
  z=0
  for _ in range(a%orders[x]):z=tab[z][x]
  return z
 def generates(xs):
  seen={0};todo=[0]
  while todo:
   z=todo.pop()
   for x in xs:
    u=tab[z][x]
    if u not in seen:seen.add(u);todo.append(u)
  return len(seen)==N
 for us in product(sing,repeat=n):
  u=0
  for x in us:u=tab[u][x]
  mult=tuple(sum(x in C for x in us) for C in cs)
  for x in range(N):
   for y in range(N):
    if tab[u][power(y,t)]!=tab[tab[x][y]][inv[x]]:continue
    if not generates((x,y)+us):continue
    counts[mult]=counts.get(mult,0)+1
 z=sum(all(tab[x][y]==tab[y][x] for y in range(N)) for x in range(N));orb=N//z
 assert all(v%orb==0 for v in counts.values())
 return {k:v//orb for k,v in counts.items()}

def main():
 saved=json.loads((ROOT/'frontier/experiments/i108_galois_tuple_divisibility/tuple-search.json').read_text());checks=0
 for name,g,p,t,n in [('S3',D['old']['group'](3),2,5,4),('A5',D['old']['group'](5,True),2,17,2),('S3xC3',D['product'](D['old']['group'](3),3),2,5,2)]:
  actual=direct(g,p,t,n);case=next(x for x in saved['cases'] if x['group']==name and x['p']==p);j=case['t'].index(t);row=next(x for x in case['results'] if x['n']==n)
  assert all(actual.get(tuple(r['multiset']),0)%case['modulus']==r['residues'][j] for r in row['rows']);checks+=1
 # The handle Nielsen map A->AB, B->B preserves the peripheral relation,
 # but not the proposed extra condition v=A^(t-1), even at admissible t=5.
 tab,inv,orders=D['old']['group'](3);A=next(i for i,o in enumerate(orders) if o==3);B=next(i for i,o in enumerate(orders) if o==2)
 def powg(x,n):
  z=0
  for _ in range(n):z=tab[z][x]
  return z
 def comm(a,b):return tab[tab[tab[a][b]][inv[a]]][inv[b]]
 v=powg(A,4);Ap=tab[A][B];assert comm(Ap,B)==comm(A,B);assert powg(Ap,4)!=v;assert tab[comm(A,B)][v]==0
 # Uniform multinomial valuation inequality and dilation invariance.
 multchecks=0
 for p in [2,3,5]:
  for s in range(0,4):
   n=p**s
   for ms in D['compositions'](n,3):
    c=factorial(n)
    for a in ms:c//=factorial(a)
    v0=D['vp'](c,p,1000);k=min(D['vp'](a,p,1000) for a in ms if a)
    assert v0+k>=s
    # Legendre: v_p((pn)!/prod(pm_i)!) = v_p(n!/prod(m_i)!).
    def vf(n):
     v=0
     while n:n//=p;v+=n
     return v
    assert vf(p*n)-sum(vf(p*a) for a in ms)==v0
    multchecks+=1
 # A5 analytic formula and its three exact Teichmuller moments.
 for s in range(1,16):
  n=2**s
  for coef,c5,bound in [(4,-2,1),(2,-2,s+3),(4,0,s+4)]:
   mod=2**(s+10);r=(pow(15,n,mod)-coef*pow(3,n,mod)+c5*pow(5,n,mod)+3)%mod
   if bound==1:assert D['vp'](r,2,s+10)==1
   else:assert D['vp'](r,2,s+10)>=bound
 assert [1-4-2+3,1-2-2+3,1-4+3]==[-2,0,0]
 return {'status':'PASS','direct_enumerations':checks,'multinomial_checks':multchecks,'A5_s_range':[1,15],'Nielsen_constraint_failure':True,'boundary':'finite checks only; universal proofs are in the report'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
