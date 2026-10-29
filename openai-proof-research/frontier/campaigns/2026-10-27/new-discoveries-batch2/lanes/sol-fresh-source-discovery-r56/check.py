import json,itertools,math
from pathlib import Path
P=Path(__file__).resolve().parent

def neighbors(m,n):
 return [sum(1<<(r*n+c) for r,c in [(i-1,j),(i+1,j),(i,j-1),(i,j+1)] if 0<=r<m and 0<=c<n) for i in range(m) for j in range(n)]
def closure(a,nb):
 while True:
  b=a
  for i,s in enumerate(nb):
   if (a&s).bit_count()>=2:b|=1<<i
  if a==b:return a
  a=b

def enumerate_grid(m,n):
 N=m*n; nb=neighbors(m,n); full=(1<<N)-1;c=[0]*(N+1)
 for a in range(1<<N):
  if closure(a,nb)==full:c[N-a.bit_count()]+=1
 return c

def step(state,mask,endpoint):
 # Frontier entries (component label, number of corners in component).
 par=list(range(4)); roots=[0]*4
 def find(i):
  while par[i]!=i:i=par[i]
  return i
 def join(i,j,edge=False):
  a,b=find(i),find(j)
  if a==b:return not edge
  par[b]=a;roots[a]+=roots[b]
  return roots[a]<=1
 for i,(lab,r) in enumerate(state):
  if lab>=0:roots[i]=r
 if state[0][0]>=0 and state[0][0]==state[1][0]:
  par[1]=0;roots[1]=0
 for i in range(2):
  if mask>>i&1:roots[2+i]=int(endpoint)
 for i in range(2):
  if state[i][0]>=0 and mask>>i&1:
   if not join(i,2+i,True):return None
 if mask==3 and not join(2,3,True):return None
 out=[];labels={}
 for i in range(2):
  if not(mask>>i&1):out.append((-1,0));continue
  r=find(2+i)
  if r not in labels:labels[r]=len(labels)
  out.append((labels[r],roots[r]))
 return tuple(out)

def strip(n):
 empty=((-1,0),(-1,0));d={empty:[1]}
 for col in range(n):
  nd={}
  for st,coeff in d.items():
   for mask in range(4):
    s=step(st,mask,col in [0,n-1])
    if s is None:continue
    t=mask.bit_count();a=nd.setdefault(s,[0]*(2*col+3))
    for k,v in enumerate(coeff):a[k+t]+=v
  d=nd
 out=[sum(a[k] for a in d.values()) for k in range(2*n+1)]
 return out

def violations(c,normalized=False):
 N=len(c)-1
 if normalized:
  return [k for k in range(1,N) if c[k]**2*(k)*(N-k)<c[k-1]*c[k+1]*(k+1)*(N-k+1)]
 return [k for k in range(1,N) if c[k]**2<c[k-1]*c[k+1]]

def main():
 rows=[]
 for m,n in [(2,j) for j in range(2,9)]+[(3,3),(3,4),(4,4)]:
  c=enumerate_grid(m,n)
  if m==2:assert c==strip(n)
  rows.append({'m':m,'n':n,'vacancy_counts':c,'LC_violations':violations(c),'ULC_violations':violations(c,True)})
 assert rows[0]['vacancy_counts']==[1,4,2,0,0]
 assert rows[1]['vacancy_counts']==[1,6,13,10,0,0,0]
 # Cubic discriminant of 10*x^3+13*x^2+6*x+1.
 a,b,c,d=10,13,6,1
 disc=b*b*c*c-4*a*c**3-4*b**3*d-27*a*a*d*d+18*a*b*c*d
 assert disc==-4
 strip_results=[]
 for n in range(2,201):
  c=strip(n);strip_results.append({'n':n,'LC_violations':violations(c),'ULC_violations':violations(c,True),'total':sum(c)})
 out={'grid_checks':rows,'strip_checks':strip_results,'cubic_discriminant':disc,'finite_evidence_only':True}
 (P/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'grids':len(rows),'strips':len(strip_results),'LC_failures':sum(bool(x['LC_violations']) for x in strip_results),'ULC_failures':sum(bool(x['ULC_violations']) for x in strip_results),'discriminant':disc}))
if __name__=='__main__':main()
