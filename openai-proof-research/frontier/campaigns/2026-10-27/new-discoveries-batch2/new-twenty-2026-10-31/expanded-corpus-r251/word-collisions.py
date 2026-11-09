from pathlib import Path
import json,sys
L=Path(__file__).resolve().parent;ix=int(sys.argv[1]);pair=json.loads((L/'word-dfs-results.json').read_text())['collisions'][ix]['words'];M=48 if ix==0 else 2*(len(pair[0]))+4
# Longer words of the other member do not change extension depth.
def counts(w):
 p=[0]
 for b in w:p.append(p[-1]+int(b))
 N=len(w);p.extend([0]*(M+1));out=[0]*(M+1)
 def go(n):
  out[n-N]+=1
  if n==N+M:return
  p[n+1]=p[n];go(n+1)
  p[n+1]=p[n]+1
  if all(p[n+1]-p[n+1-k]<=p[k] for k in range(1,n+2)):go(n+1)
 go(N);return out
A=counts(pair[0]);B=counts(pair[1]);diff=[i for i in range(1,M+1) if A[i]!=B[i]]
res={'pair':pair,'max_extension':M,'a':A,'b':B,'first_difference':diff[0] if diff else None}
(L/f'word-collision-{ix}.json').write_text(json.dumps(res,indent=2));print(res)
