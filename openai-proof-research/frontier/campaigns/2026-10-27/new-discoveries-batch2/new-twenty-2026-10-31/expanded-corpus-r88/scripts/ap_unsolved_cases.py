# Targeted search inside the two cases left unsolved by Kumar-Mohan-Pandey (Integers 26 (2026) #A58, Theorem 2):
# X1 = {d1*i : 0<=i<n}, X2 = {b + d2*j : 0<=j<m}, min X2 < max X1, d1 != d2, with
# (b/d1 frac = p1/q1, d2/d1 frac = p2/q2) and either gcd(q1,q2)>1 or (q1==2 and gcd(2,q2)==1), and 0<d2<(n-1)d1.
import sys,time,json
from math import gcd
D1=int(sys.argv[1]); D2F=int(sys.argv[2]); L=int(sys.argv[3])
def sizes(el):
    m=min(el); el=[x-m for x in el]; M=0
    for x in el: M|=1<<x
    top=max(el); R=0
    for x in el: R|=1<<(top-x)
    s=0; df=0
    for x in el: s|=M<<x; df|=R<<x
    return bin(s).count('1'), bin(df).count('1')
def q(num,den):
    g=gcd(num%den,den); return den//g if num%den else 1
t=time.time(); cnt=0; best=None; found=[]; seen=set()
for d1 in range(2,D1+1):
  for n in range(3,L+1):
    A=[d1*i for i in range(n)]
    for d2 in range(1,min(D2F*d1,(n-1)*d1)):
      if d2==d1: continue
      q2=q(d2,d1)
      for m in range(2,L+1):
        for b in range(-(m-1)*d2+1,(n-1)*d1):   # min X2 = b < max X1
          if b<0 and b+(m-1)*d2<0: continue
          q1=q(b,d1)
          if q1==1 or q2==1: 
            if not (q1==2 and q2%2==1 and q2>1): continue
          if not (gcd(q1,q2)>1 or (q1==2 and q2%2==1)): continue
          S=sorted(set(A+[b+d2*j for j in range(m)]))
          key=tuple(x-S[0] for x in S)
          if key in seen: continue
          seen.add(key); cnt+=1
          ps,pd=sizes(key); g=ps-pd
          if best is None or g>best[0]: best=(g,key,(d1,n,b,d2,m))
          if g>0: found.append((key,(d1,n,b,d2,m),ps,pd))
print(json.dumps({'D1max':D1,'d2_lt_factor_times_d1':D2F,'Lmax':L,'distinct_sets':cnt,'best_gap':best[0] if best else None,'best':best,'num_sum_dominant':len(found),'examples':found[:5],'secs':time.time()-t}))
