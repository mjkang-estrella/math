#!/usr/bin/env python3
from pathlib import Path
import json
N=350
rows=[[1]];checks=0
for n in range(1,N+1):
 prev=rows[-1];rows.append([0]+[(n-k+1)*prev[k-1]+k*(prev[k] if k<len(prev) else 0) for k in range(1,n+1)])
 out=[sum(rows[n][k]*(rows[k][j] if j<len(rows[k]) else 0) for k in range(n+1)) for j in range(n+1)]
 for j in range(2,n):
  checks+=1
  # Remove one zero root: degree n-1, coefficients indexed j-1.
  if out[j]**2*(j-1)*(n-j) < out[j-1]*out[j+1]*j*(n-j+1):
   print('NEWTON FAILURE',n,j,flush=True);Path('eulerian-screen.json').write_text(json.dumps({'n':n,'j':j,'row':out}));raise SystemExit
 if n%50==0:print('through',n,flush=True)
Path('eulerian-screen.json').write_text(json.dumps({'status':'no Newton failure','through_n':N,'checks':checks})+'\n')
print('No failure',N,checks)
