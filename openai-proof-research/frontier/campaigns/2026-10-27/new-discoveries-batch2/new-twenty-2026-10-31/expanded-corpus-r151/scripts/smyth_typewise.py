# Type-wise test: for each type p (multiset, A+B cells), #arrangements with first-A sum b <= with first-A sum a.
import sys,collections
from math import factorial
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth import parts_count, combine
M=int(sys.argv[1]); W=int(sys.argv[2])
fails=0;cnt=0;ex=[]
for A in range(1,M+1):
  for B in range(0,A+1):
    for a in range(0,W+1):
      for b in range(0,a):
        X=combine(parts_count(b,A),parts_count(a,B)); Y=combine(parts_count(a,A),parts_count(b,B))
        for p,v in X.items():
          cnt+=1
          if v>Y.get(p,0):
            fails+=1
            if len(ex)<15: ex.append((A,a,B,b,p,v,Y.get(p,0)))
print('typechecks',cnt,'typewise_fail',fails)
for e in ex: print(e)
