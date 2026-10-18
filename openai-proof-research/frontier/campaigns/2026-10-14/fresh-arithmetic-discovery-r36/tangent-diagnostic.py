#!/usr/bin/env python3
"""MIT. Finite tangent-rank diagnostic; not an orbit or arithmetic certificate."""
import json
P=1009

def eye(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def zero(n):return [[0]*n for _ in range(n)]
def mm(a,b):
 n=len(a);return [[sum(a[i][k]*b[k][j] for k in range(n))%P for j in range(n)] for i in range(n)]
def add(a,b):return [[(x+y)%P for x,y in zip(u,v)] for u,v in zip(a,b)]
def scale(a,c):return [[x*c%P for x in row] for row in a]
def inv(a):
 n=len(a);w=[a[i][:]+eye(n)[i] for i in range(n)]
 for i in range(n):
  j=next(j for j in range(i,n) if w[j][i]);w[i],w[j]=w[j],w[i];t=pow(w[i][i],-1,P);w[i]=[x*t%P for x in w[i]]
  for j in range(n):
   if j!=i:
    t=w[j][i];w[j]=[(x-t*y)%P for x,y in zip(w[j],w[i])]
 return [row[n:] for row in w]
def rank(rows):
 a=[row[:] for row in rows];r=0
 for j in range(len(a[0])):
  k=next((k for k in range(r,len(a)) if a[k][j]),None)
  if k is None:continue
  a[k],a[r]=a[r],a[k];t=pow(a[r][j],-1,P);a[r]=[x*t%P for x in a[r]]
  for k in range(r+1,len(a)):
   if a[k][j]:
    t=a[k][j];a[k]=[(x-t*y)%P for x,y in zip(a[k],a[r])]
  r+=1
  if r==len(a):break
 return r

def one(n):
 I=eye(n);basis=[]
 for i in range(n):
  for j in range(n):
   if i!=j:x=zero(n);x[i][j]=1;basis.append(x)
 for i in range(n-1):x=zero(n);x[i][i]=1;x[-1][-1]=P-1;basis.append(x)
 def diag(v):
  z=1
  for x in v:z=z*x%P
  v=v+[pow(z,-1,P)];return [[v[i] if i==j else 0 for j in range(n)] for i in range(n)]
 A=diag(list(range(2,n+1)));B=diag(list(range(n+2,2*n+1)))
 C=[[int(i==(j+1)%n) for j in range(n)] for i in range(n)];E=eye(n);E[0][1]=3;C=mm(C,E)
 if n%2==0:C[0]=[(-x)%P for x in C[0]]
 mats=[A,B,C,I];mis=[inv(x) for x in mats]
 def parts(word):
  fac=[mats[s] if sign==1 else mis[s] for s,sign in word];pre=[I]
  for f in fac:pre.append(mm(pre[-1],f))
  suf=[None]*(len(fac)+1);suf[-1]=I
  for j in range(len(fac)-1,-1,-1):suf[j]=mm(fac[j],suf[j+1])
  return fac,pre,suf
 rel=[(0,1),(1,1),(0,-1),(1,-1),(2,1),(3,1),(2,-1),(3,-1)]
 fac,pre,suf=parts(rel);assert pre[-1]==I
 columns=[]
 for s in range(4):
  for x in basis:
   total=zero(n)
   for j,(t,sign) in enumerate(rel):
    if t==s:
     df=mm(x,mats[s]) if sign==1 else scale(mm(mis[s],x),-1)
     total=add(total,mm(mm(pre[j],df),suf[j+1]))
   columns.append(sum(total,[]))
 R=[list(x) for x in zip(*columns)];rr=rank(R)
 groups={};allrows=[]
 for name,typ in [('basic',None),('a^k b c^l d',(0,2)),('a b^k c^l d',(1,2)),('a^k b c d^l',(0,3)),('a b^k c d^l',(1,3))]:
  if typ is None:words=[[(s,1)] for s in range(4)]
  else:
   words=[]
   for k in range(0,2*n+1):
    for l in range(0,2*n+1):
     counts=[1]*4;counts[typ[0]]=k;counts[typ[1]]=l
     words.append([(s,1) for s in range(4) for _ in range(counts[s])])
  rows=[]
  for w in words:
   fac,pre,suf=parts(w);power=I
   for j in range(1,n):
    grads=[zero(n) for _ in range(4)]
    for pos,(s,sign) in enumerate(w):
     assert sign==1
     z=mm(mm(mm(mats[s],suf[pos+1]),power),pre[pos]);grads[s]=add(grads[s],z)
    row=[]
    for z in grads:
     row.extend(j*z[b][a]%P for a in range(n) for b in range(n) if a!=b)
     row.extend(j*(z[a][a]-z[-1][-1])%P for a in range(n-1))
    rows.append(row);power=mm(power,pre[-1])
  allrows+=rows;groups[name]={'new_rows':len(rows),'cumulative_cotangent_rank':rank(R+allrows)-rr}
 return {'rank':n,'prime':P,'relation_rank':rr,'expected_relation_rank':n*n-1,'character_dimension':2*(n*n-1),'groups':groups,'limit':'Finite-field test point with diagonal determinant correction; no all-rank characteristic-zero or band-monodromy torus-generation claim.'}
if __name__=='__main__':print(json.dumps({'status':'COMPLETED','cases':[one(n) for n in range(2,5)]},indent=2))
