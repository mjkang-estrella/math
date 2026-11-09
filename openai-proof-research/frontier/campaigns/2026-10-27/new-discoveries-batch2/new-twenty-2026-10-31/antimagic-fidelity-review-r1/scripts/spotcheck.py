from pathlib import Path
import json
# Independent transcription of the frozen Nat formula; subtraction is truncated.
def sub(a,b):return max(0,a-b)
def lab(t,n,h,i,patch=True):
 if n==1:return i+1
 if n==2:
  if t==2:return ([1,4] if h==1 else [2,3,6,5])[i]
  s=t//2
  if h==1:return 2 if i==0 else sub(3*s+2,i)
  p,j=divmod(i,t)
  if p==0:return 1 if j==0 else j+2 if j<=s else 2*s+1+j
  a=p-1;k=s-1;q=t-1;beta=2*t+(s-1)*q
  if j<t-2:
   b=j//2
   return 2*t+b*q+a+1 if j%2==0 else 2*t+(t-1-b)*q+sub(q,a)
  if a<=k:return beta+2*a+1 if j==t-2 else sub(beta+3*k+2,a)
  r=a-k
  return beta+2*r if j==t-2 else sub(beta+4*k+3,r)
 N=sum(t**g for g in range(1,n));Z=sub(N,t)//2+1
 def internal(h,i):
  if h==1:return Z if i==0 else sub(N,t)+1+i
  if patch and t==2 and h==2 and i in (1,3):i=4-i
  r=sum(t**g for g in range(h+1,n))+i;d=1+r//2
  return sub(Z,d) if r%2==0 else Z+d
 if h<n:return internal(h,i)
 q=t**(n-1);pl=internal(n-1,i//t)
 a=sub(pl,Z) if Z<pl else sub(q+1+pl,Z);j=i%t
 def lam(b,x):return N+sub(b,1)*q+x
 if j<t-2:
  b=j//2+1
  return lam(b,a) if j%2==0 else lam(sub(t+1,b),sub(q+1,a))
 if j==t-2:return lam(t//2,a)
 sigma=2*a if a<=q//2 else 2*sub(a,q//2)-1
 return lam(t//2+1,sub(q+1,sigma))
def test(t,n,patch=True,duplicate=False):
 edges=[((h-1,i//t),(h,i),lab(t,n,h,i,patch)) for h in range(1,n+1) for i in range(t**h)]
 if duplicate:edges[1]=(edges[1][0],edges[1][1],edges[0][2])
 labels=[e[2] for e in edges];w={(0,0):0};degrees={(0,0):0}
 for u,v,a in edges:
  for x in (u,v):w[x]=w.get(x,0)+a;degrees[x]=degrees.get(x,0)+1
 return {'t':t,'n':n,'edges':len(edges),'bijection':sorted(labels)==list(range(1,len(edges)+1)), 'proper':all(w[u]!=w[v] for u,v,_ in edges),'colors':len(set(w.values())),'expected':t**n+1,'leaves':sum(d==1 for d in degrees.values())}
rows=[]
for t in (2,4,6):
 for n in range(1,9):
  if sum(t**h for h in range(1,n+1))>500000:break
  r=test(t,n);assert r['bijection'] and r['proper'] and r['colors']==r['expected'] and r['leaves']==t**n;r['status']='PASS';rows.append(r)
neg=[test(2,3,False),test(4,3,duplicate=True)]
assert not neg[0]['proper'] and not neg[1]['bijection']
L=Path(__file__).resolve().parents[1];(L/'evidence/spotcheck.json').write_text(json.dumps({'cases':rows,'negative_controls':neg},indent=2));print(json.dumps({'cases':len(rows),'all_pass':True,'negative_controls_detected':True}))
