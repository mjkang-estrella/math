# 374787: look for (a,b,c,m) where an unsorted exponent permutation has divisor density >= 1
# but the sorted permutation has plain density sum_{d | L, d >= m} 1/d < 1 (then no covering).
from fractions import Fraction as F
import itertools
def dens(e,m):
    a,b,c=e; s=F(0)
    for i in range(a+1):
        for j in range(b+1):
            for k in range(c+1):
                d=2**i*3**j*5**k
                if d>=m: s+=F(1,d)
    return s
hits=[]
for a in range(1,9):
  for b in range(1,a+1):
    for c in range(1,b+1):
      srt=(a,b,c)
      for m in range(2,200):
        ds=dens(srt,m)
        if ds>=1: continue
        for p in set(itertools.permutations(srt)):
          if p==srt: continue
          dp=dens(p,m)
          if dp>=1: hits.append((srt,p,m,float(ds),float(dp)))
print(len(hits))
for h in hits[:40]: print(h)
