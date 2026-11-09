"""Exact polynomial diagnostics, never a proof of the unbounded conjecture."""
import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
import itertools, json, pathlib, math
P=pathlib.Path(__file__).resolve().parent

def tables(s,p):
 assert len(s)==2 and len(p)<=6 and sum(s)==sum(p)<=30
 for a in itertools.product(*(range(x+1) for x in p)):
  if sum(a)==s[0]:yield a

def literal(a,p):
 # Direct source row insertion, independent of greedy shortcut.
 rows=[];q=[]
 for j in range(len(p)):
  for v in [0]*a[j]+[1]*(p[j]-a[j]):
   r=0
   while True:
    if r==len(rows):rows.append([]);q.append([])
    col=next((i for i,x in enumerate(rows[r]) if x>v),len(rows[r]))
    if col==len(rows[r]):rows[r].append(v);q[r].append(j);break
    rows[r][col],v=v,rows[r][col];r+=1
 return rows,q

def greedy(a,p):
 B=0;c=[]
 for x,y in zip(a,p):
  z=min(x,B);c.append(z);B=B-z+y-x
 C=sum(c);s=sum(a)
 return [[0]*s+[1]*B]+([[1]*C] if C else []),[[j for j,y in enumerate(p) for _ in range(y-c[j])]]+([[j for j,z in enumerate(c) for _ in range(z)]] if C else [])

def expand(rows,q,n):
 # Dictionary indexes are row-one exponents; row-two exponents fixed by p.
 out={(0,)*n:1}
 for k in range(len(rows[0])):
  if len(rows)>1 and k<len(rows[1]):
   j,l=q[0][k],q[1][k];assert j<l
   terms=[(j,1),(l,-1)]
  else:terms=[(q[0][k] if rows[0][k]==0 else None,1)]
  nxt={}
  for a,v in out.items():
   for j,w in terms:
    z=list(a)
    if j is not None:z[j]+=1
    z=tuple(z);nxt[z]=nxt.get(z,0)+v*w
  out={a:v for a,v in nxt.items() if v}
 return out

def matrix(s,p):
 ts=list(tables(s,p));idx={a:i for i,a in enumerate(ts)};N=len(ts);assert N<=100
 A=[[0]*N for _ in ts]
 for k,a in enumerate(ts):
  direct=literal(a,p);fast=greedy(a,p);assert direct==fast,(s,p,a,direct,fast)
  for b,v in expand(*direct,len(p)).items():A[idx[b]][k]=v
 return ts,A

def mul(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def tr(A):return sum(A[i][i] for i in range(len(A)))
def subid(A):return [[v-(i==j) for j,v in enumerate(row)] for i,row in enumerate(A)]
def traces(A):
 B=mul(A,A);C=mul(B,B)
 return [len(A),tr(A),tr(B),tr(C)]

def main():
 checks=[]
 # All positive 2x3 reduced pairs only through degree 8; finite diagnostic.
 for d in range(3,9):
  for p in itertools.product(range(1,d-1),repeat=3):
   if sum(p)!=d:continue
   for a in range(1,d):
    s=(a,d-a)
    if max(p)>min(s):continue
    ts,A=matrix(s,p);tri=s[0]==p[0]
    if tri:assert mul(A,A)==[[int(i==j) for j in range(len(A))] for i in range(len(A))]
    checks.append({'s':s,'p':p,'triangular':tri,'moments_N_tr1_tr2_tr4':traces(A)})
 # Selected infinite-family members: not a separate new theorem.
 families=[]
 for n in range(3,7):
  p=(2,)*n;s=(2*n-2,2)
  ts,A=matrix(s,p);families.append({'n':n,'moments':traces(A)})
 # Known exact Table6 entry validates orientation and coefficients.
 import sympy as S
 t=S.Symbol('t');ts,A=matrix((2,2),(1,2,1))
 assert S.Matrix(A).charpoly(t).as_expr().expand()==S.expand((t-1)*(t+1)*(t*t-t-1))
 result={'status':'PASS','coverage':'all positive reduced 2x3 degree3..8, plus n3..6 Zhang family; no global conclusion','pairs':len(checks),'nontriangular':sum(not x['triangular'] for x in checks),'second_moment_blind':[x for x in checks if not x['triangular'] and x['moments_N_tr1_tr2_tr4'][0]==x['moments_N_tr1_tr2_tr4'][2]],'fourth_moment_blind':[x for x in checks if not x['triangular'] and x['moments_N_tr1_tr2_tr4'][0]==x['moments_N_tr1_tr2_tr4'][3]],'checks':checks,'known_family':families,'table6':{'basis':ts,'matrix':A,'charpoly':str(S.Matrix(A).charpoly(t).as_expr().factor())}}
 (P/'checks.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ['checks','second_moment_blind','fourth_moment_blind']},indent=2));print('second blind',len(result['second_moment_blind']),'fourth blind',len(result['fourth_moment_blind'])); print('first second blind',result['second_moment_blind'][:3])
if __name__=='__main__':main()
