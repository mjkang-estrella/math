"""Exact finite diagnostics; not a proof of general elementary unimodality."""
from pathlib import Path
from collections import Counter,deque
from fractions import Fraction
from functools import lru_cache
from itertools import combinations,combinations_with_replacement,product
import json,hashlib
OUT=Path(__file__).resolve().parent

def parts(n,m=None):
 if n==0:yield ();return
 for a in range(min(n,m or n),1-1,-1):
  for p in parts(n-a,a):yield (a,)+p

def hessenbergs(n):
 def rec(h):
  i=len(h)+1
  if i>n:yield tuple(h);return
  for v in range(max(i,h[-1] if h else 1),n+1):yield from rec(h+[v])
 yield from rec([])

@lru_cache(None)
def em_coeff(lam,mu):
 if not lam:return int(not any(mu))
 ans=0
 for inds in combinations([i for i,v in enumerate(mu) if v],lam[0]):
  a=list(mu)
  for i in inds:a[i]-=1
  ans+=em_coeff(lam[1:],tuple(a))
 return ans

def inverse(A):
 n=len(A);T=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(n)]for i,row in enumerate(A)]
 for j in range(n):
  k=next(i for i in range(j,n)if T[i][j]);T[j],T[k]=T[k],T[j];v=T[j][j];T[j]=[a/v for a in T[j]]
  for i in range(n):
   if i!=j:
    v=T[i][j];T[i]=[a-v*b for a,b in zip(T[i],T[j])]
 return [r[n:]for r in T]

@lru_cache(None)
def basis(n):
 ps=list(parts(n));A=[[em_coeff(lam,mu)for lam in ps]for mu in ps];I=inverse(A)
 assert all(x.denominator==1 for r in I for x in r)
 I=[[int(x)for x in r]for r in I]
 assert all(sum(A[i][k]*I[k][j]for k in range(len(ps)))==int(i==j)for i in range(len(ps))for j in range(len(ps)))
 return ps,A,I

def monomial(h,mu):
 n=len(h);M=sum(v-i-1 for i,v in enumerate(h));out=[0]*(M+1);left=list(mu);word=[];nbr=[[i for i in range(j)if j<h[i]]for j in range(n)]
 def rec(j,asc):
  if j==n:out[asc]+=1;return
  bad={word[i]for i in nbr[j]}
  for c in range(len(mu)):
   if left[c] and c not in bad:
    left[c]-=1;inc=sum(word[i]<c for i in nbr[j]);word.append(c);rec(j+1,asc+inc);word.pop();left[c]+=1
 rec(0,0);return out

def ecoeff(h):
 ps,A,I=basis(len(h));ms=[monomial(h,p)for p in ps];M=len(ms[0]);cs=[[sum(I[i][k]*ms[k][d]for k in range(len(ps)))for d in range(M)]for i in range(len(ps))]
 assert all(sum(A[k][i]*cs[i][d]for i in range(len(ps)))==ms[k][d]for k in range(len(ps))for d in range(M))
 return dict(zip(ps,cs))

def qmul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def graph_checks():
 counts=[];nonzero=0;ineq=0;records=[]
 for n in range(1,8):
  cnt=0
  for h in hessenbergs(n):
   cs=ecoeff(h);M=sum(v-i-1 for i,v in enumerate(h));total=[sum(c[d]for c in cs.values())for d in range(M+1)]
   digit=[1]
   for j in range(n):digit=qmul(digit,[1]*(sum(j<h[i]for i in range(j))+1))
   assert total==digit
   for lam,c in cs.items():
    assert min(c)>=0 and c==c[::-1]
    if any(c):nonzero+=1
    for d in range((M+1)//2):assert c[d+1]>=c[d];ineq+=1
   records.append([h,[[lam,c]for lam,c in cs.items()if any(c)]]);cnt+=1
  counts.append([n,cnt])
  print('graphs complete',n,cnt,flush=True)
 (OUT/'graph-coefficients.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
 return dict(counts=counts,nonzero_coefficients=nonzero,inequalities=ineq,enumeration='proper colorings with prescribed color multiplicities; exact e-to-m inverse; no source witness implementation',sha256=hashlib.sha256((OUT/'graph-coefficients.json').read_bytes()).hexdigest())

def char(r):return Counter({i:1 for i in range(-r,r+1,2)})
def conv(a,b):
 c=Counter()
 for i,x in a.items():
  for j,y in b.items():c[i+j]+=x*y
 return +c

def powers(weights,j,exterior):
 its=combinations(weights,j)if exterior else combinations_with_replacement(weights,j)
 return Counter(sum(a)for a in its)

def lef(p):
 if not p:return {}
 assert all(p[i]==p[-i]for i in p)
 out={r:p[r]-p[r+2]for r in range(max(p)+1)}
 assert min(out.values())>=0
 assert all(sum(v for r,v in out.items()if abs(i)<=r and (r-i)%2==0)==p[i]for i in range(-max(p),max(p)+1))
 return {r:v for r,v in out.items()if v}

def rectangle(a,b):
 """Symmetric chains for product of chains on 0..a and 0..b."""
 ans=[];lo=0;right=a
 while lo<=b and right>=0:
  ans.append([(x,lo)for x in range(right+1)]+[(right,y)for y in range(lo+1,b+1)])
  lo+=1;right-=1
 return ans

def local_checks():
 nc=0;pc=0
 for v in (Fraction(2),Fraction(3,2),Fraction(5,3)):
  for j in range(1,13):
   logd=lambda v:Fraction((-1)**(j+1),j)/(v**j-v**(-j))
   assert logd(v)==-logd(1/v)
 for a in range(1,9):
  centered=list(range(1-a,a,2))
  for k in range(-5,5):
   for eps in (-1,1):
    t=eps*a
    letters=list(range(1,a+1))if t>0 else list(range(t+1,1))
    shifted=[k+2*l-t for l in letters]
    assert sorted(shifted)==[k+1+w for w in centered]
    for E in (False,True):
     for j in range(0,min(a,4)+1):
      p=powers(shifted,j,E);q=powers(centered,j,E)
      assert p==Counter({w+j*(k+1):v for w,v in q.items()});lef(q);nc+=1
 for a in range(1,6):
  for b in range(1,6):
   weights=[x+y for x in char(a-1)for y in char(b-1)]
   for E in (True,False):
    for j in range(4):lef(powers(weights,j,E));pc+=1
 for a in range(10):
  for b in range(10):
   chains=rectangle(a,b);points=[p for c in chains for p in c]
   assert len(points)==len(set(points))==(a+1)*(b+1)
   for c in chains:
    assert sum(c[0])+sum(c[-1])==a+b
    assert all(sum(y)-sum(x)==1 and all(v>=u for u,v in zip(x,y))for x,y in zip(c,c[1:]))
 # Two valid positive elementary units on one ray with parameters 1,-3.
 # At pairing 1 their one-jump sum is v^2+v^-2: positive reciprocal, not Lefschetz.
 p=Counter({2:1,-2:1});assert p[0]-p[2]==-1
 return dict(unit_shift_cases=nc,centered_packet_cases=pc,rectangle_cases=100,allowed_wall_counterexample={'units':['E(p,1)','E(p,-3)'],'pairing':1,'one_jump':{'-2':1,'2':1},'trivial_character_multiplicity':-1},weyl_truncation={'relation':'[D,T]=1','on_Q[x]/(x^(r+1))':'D does not descend: D(x^(r+1))=(r+1)x^r','truncated_top_commutator':'[D,T]x^r=-r x^r, not x^r'})

def mutation_checks():
 B=((0,-2,0,1,0),(2,0,-1,-1,1),(0,1,0,-1,-1),(-1,1,1,0,-1),(0,-1,1,1,0))
 def mut(b,k):return tuple(tuple(-b[i][j]if k in(i,j)else b[i][j]+max(b[i][k],0)*max(b[k][j],0)-max(-b[i][k],0)*max(-b[k][j],0)for j in range(5))for i in range(5))
 def acyclic(b):
  s=set(range(5))
  while s:
   roots=[i for i in s if all(b[j][i]<=0 for j in s)]
   if not roots:return False
   s.difference_update(roots)
  return True
 Q=deque([(B,())]);seen={B};discard=0;largest=2;maxdepth=0;found=[]
 while Q:
  b,w=Q.popleft();maxdepth=max(maxdepth,len(w))
  if acyclic(b):found.append(w)
  for k in range(5):
   if w and w[-1]==k:continue
   c=mut(b,k);assert mut(c,k)==b
   cap=max(abs(x)for r in c for x in r);largest=max(largest,cap)
   if cap>6:discard+=1;continue
   if c not in seen:seen.add(c);Q.append((c,w+(k,)))
 return dict(initial_matrix=B,entry_cap=6,states=len(seen),discarded_edges=discard,largest_discarded_entry=largest,max_bfs_depth=maxdepth,acyclic_sequences=found,interpretation='only the component reachable with EVERY intermediate entry bounded by 6 was exhausted; no unrestricted impossibility claim')

def main():
 results=dict(local=local_checks(),mutation=mutation_checks(),graphs=graph_checks())
 (OUT/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()
