#!/usr/bin/env python3
"""MIT. Pieri arithmetic for the proved long-arm route exclusions."""
import json

def addbox(lam):
 out=[]
 for i in range(len(lam)+1):
  x=list(lam)+( [0] if i==len(lam) else [])
  if i and x[i]==x[i-1]:continue
  x[i]+=1;out.append(tuple(x))
 return out

def terms(A,B):
 if not B:return [(A,)]
 return [(A+1,)+(1,)*(B-1),(A,)+(1,)*B]

def main():
 tables=[]
 for K in range(7,41):
  hook=[sum(len(lam)<=4 for lam in terms(K-B,B)) for B in range(5)]
  extra=[sum(len(nu)<=4 for lam in terms(K-B-1,B) for nu in addbox(lam)) for B in range(5)]
  assert hook==[1,2,2,2,1] and extra==[2,5,6,5,2]
  tables.append({'K':K,'hook':hook,'extra_cell':extra,'hook_total':sum(hook),'near_hook_total':sum(hook)+sum(extra)})
 for m in range(10,301):
  N=m*(m+1)//2;K=2*m-1;a=(N+1)//2;b=N-a
  assert a>K and b>=4 and a>m and b+1>m and 8<m-1
 for m in range(30,301):
  N=m*(m+1)//2;K=2*m-1;a=N//2;b=N-a-2
  assert a>=K+2 and b>=6 and b+2>=K+2 and a-2>=6 and 28<m-1
 return {'status':'PASS finite Pieri and parameter checks; general arguments in exploratory-screen-205.md','tables':tables,'hook_m_range':[10,300],'near_hook_m_range':[30,300]}
if __name__=='__main__':print(json.dumps(main(),indent=2))
