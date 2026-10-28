#!/usr/bin/env python3
"""Exact O(N^3) count checks; never constructs ordered set partitions."""
from math import comb
from pathlib import Path
import json

N=101
# C[n][l] counts ordered odd-block set compositions of [n] with l blocks.
C=[[0]*(N+1) for _ in range(N+1)]
C[0][0]=1
for n in range(1,N+1):
    for l in range(1,n+1):
        C[n][l]=sum(comb(n,r)*C[n-r][l-1] for r in range(1,n+1,2))

E=[1]
rhs={}
for n in range(1,N+1):
    old=E
    E=[(k+1)*(old[k] if k<len(old) else 0)+(n-k)*(old[k-1] if k else 0)
       for k in range(n)]
    rhs[n]=sum((-1)**k*v for k,v in enumerate(E))

def mu_next(l):
    assert l%2==1
    k=(l-1)//2
    return (-1)**k*comb(2*k,k)//(k+1)

rows=[]
for n in range(1,N+1,2):
    lhs=sum(2**(n-l)*mu_next(l)*C[n][l] for l in range(1,n+1,2))
    assert lhs==rhs[n],(n,lhs,rhs[n])
    rows.append({'n':n,'value':str(lhs)})
result={'status':'PASS finite diagnostics only; source explicitly already resolved',
        'max_n':N,'cases':len(rows),'allocated_count_cells':(N+1)**2,
        'partitions_materialized':0,'rows':rows}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
