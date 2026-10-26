#!/usr/bin/env python3
"""Supporting exact screening of corrected Hart--Rowley recurrences, credit0."""
from pathlib import Path
import argparse,itertools,json

def add(*ps):
 o=[0]*max(map(len,ps))
 for p in ps:
  for i,a in enumerate(p):o[i]+=a
 while len(o)>1 and not o[-1]:o.pop()
 return o
def shift(p,s):return [0]*s+p
# Multiply by q*(1+q²+...+q^(2(k-1))) via parity prefix sums.
def odd_interval(p,k):
 o=[0]*(len(p)+2*k-1)
 for r in [0,1]:
  total=0
  for j in range(r,len(o),2):
   if j-1>=0 and j-1<len(p):total+=p[j-1]
   if j-1-2*k>=0 and j-1-2*k<len(p):total-=p[j-1-2*k]
   o[j]=total
 return o

def involutions(n):
 p=list(range(n))
 def rec(left):
  if not left:
   yield p[:];return
  i=left[0];tail=left[1:]
  p[i]=i;yield from rec(tail)
  for j in tail:
   p[i]=j;p[j]=i;yield from rec([a for a in tail if a!=j]);p[j]=j
  p[i]=i
 yield from rec(list(range(n)))

def enumerate_signed(n):
 B=[0]*(n*n+1);D=[0]*(n*(n-1)+1);O=D[:]
 for p in involutions(n):
  cycles=[(i,) if i==p[i] else (i,p[i]) for i in range(n) if i<=p[i]]
  for signs in itertools.product([1,-1],repeat=len(cycles)):
   v=[0]*n
   for I,s in zip(cycles,signs):
    for i in I:v[i]=s*(p[i]+1)
   inv=sum(v[i]>v[j] for i in range(n) for j in range(i+1,n))
   neg=sum(t<0 for t in v);pairs=sum(v[i]+v[j]<0 for i in range(n) for j in range(i+1,n))
   B[inv+neg+pairs]+=1
   (D if neg%2==0 else O)[inv+pairs]+=1
 while len(B)>1 and not B[-1]:B.pop()
 while len(D)>1 and not D[-1]:D.pop()
 while len(O)>1 and not O[-1]:O.pop()
 return B,D,O

def violation(p,parity):
 a=p[parity::2];down=False
 for i in range(1,len(a)):
  if a[i]<a[i-1]:down=True
  if down and a[i]>a[i-1]:return {'degree':parity+2*i,'rise_pair':[a[i-1],a[i]]}
 return None

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=150);args=ap.parse_args()
 B={1:[1,1],2:[1,2,0,2,1]};D={1:[1],2:[1,2,1]};O={1:[1],2:[1,0,1]}
 A0=[1];A1=[1];hits=[];checks=0;anchors=[];Achecks=0
 for n in range(2,args.n+1):
  A=add(A1,odd_interval(A0,n-1));A0,A1=A1,A
  for i in range(2,len(A)-2):
   Achecks+=1
   if A[i]**2<A[i-2]*A[i+2]:hits.append({'family':'A_parity_LC','n':n,'degree':i,'triple':[A[i-2],A[i],A[i+2]]})
  if n>=3:
   B[n]=add(B[n-1],shift(B[n-1],2*n-1),odd_interval(B[n-2],2*n-2))
   qD=odd_interval(D[n-2],n-1);qO=odd_interval(O[n-2],n-1)
   D[n]=add(D[n-1],shift(O[n-1],2*n-2),qD,shift(qD,2*n-4))
   O[n]=add(O[n-1],shift(D[n-1],2*n-2),qO,shift(qO,2*n-4))
  if n<=7:
   e=enumerate_signed(n);assert e==(B[n],D[n],O[n]),n;anchors.append({'n':n,'signed_involutions':sum(e[0])})
  for f,p in [('B',B[n]),('D',D[n]),('O',O[n])]:
   for parity in [0,1]:
    checks+=1;v=violation(p,parity)
    if v:hits.append({'family':f,'n':n,'parity':parity,**v})
  if n>3:
   for tab in [B,D,O]:del tab[n-2]
 out={'status':'SCREEN ONLY','max_n':args.n,'parity_unimodality_cases':checks,'A_parity_LC_inequalities':Achecks,'independent_enumeration_anchors':anchors,'failures':hits,'qualification':'Known B6 even failure is published Hart--Rowley, never a new discovery. No formal proof or novelty claim. D2=1+2q+q² is directly enumerated; source2014Cor4.1(c) omits q² in an initial-value typo.'}
 Path(__file__).with_name('parity-screen.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
