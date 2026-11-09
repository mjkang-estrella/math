import json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1];N=int(sys.argv[1]);P=[{},{}];tested=0;valid=0;bad=[]
def isp(w):return w==w[::-1]
def closure(s):
 for k in range(len(s)+1):
  if isp(s[k:]):return s+s[:k][::-1]
def directive(w):
 v='';u=''
 while len(v)<len(w):
  a=w[len(v)];v=closure(v+a);u+=a
  if not w.startswith(v):return None
 return u
for n in range(3,N+1):
 for a in range(1,n-1):
  for b in range(1,n-a):
   c=n-a-b;tested+=1
   lf=list(range(a+b,n))+list(range(a,a+b))+list(range(a));L='c'*c+'b'*b+'a'*a
   i=0;seq=[]
   while True:
    seq.append(L[i]);i=lf[i]
    if i==0:break
   if len(seq)!=n:continue
   w=''.join(seq[::-1]);valid+=1
   assert w[0]=='a' and w[-1]=='c'
   fs=[(w[1:k],w[k+1:-1]) for k in range(1,n-1) if w[k]=='b' and isp(w[1:k]) and isp(w[k+1:-1])]
   assert len(fs)==1
   for j,v in enumerate(fs[0]):
    if v in P[j]:continue
    P[j][v]=w
    if v in P[1-j]:
     u=directive(v)
     if u is None or ('b' in u and set(u[u.index('b'):])!={'b'}):bad.append({'palindrome':v,'directive':u,'witness_P1':P[0][v],'witness_P2':P[1][v]});print('BAD',bad[-1],flush=True)
 if n%10==0 or n==N:
  r={'max_witness_length':n,'positive_parikh_vectors_tested':tested,'primitive_perfectly_clustering_lyndon_words':valid,'P1_count':len(P[0]),'P2_count':len(P[1]),'intersection':len(P[0].keys()&P[1].keys()),'counterexamples':bad};print(r,flush=True);(D/f'outputs/pal-bwt-{N}.json').write_text(json.dumps(r,indent=2)+'\n')
