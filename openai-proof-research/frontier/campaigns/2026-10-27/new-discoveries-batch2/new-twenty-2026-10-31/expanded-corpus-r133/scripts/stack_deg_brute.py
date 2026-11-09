# exact d_n = (1/n!) sum_y |s^{-1}(y)|^2 for small n by brute force over S_n
import itertools, sys, math
from collections import Counter
def s(p):
    st=[];out=[]
    for x in p:
        while st and st[-1]<x: out.append(st.pop())
        st.append(x)
    while st: out.append(st.pop())
    return tuple(out)
N=int(sys.argv[1])
prev=None
for n in range(1,N+1):
    c=Counter(s(p) for p in itertools.permutations(range(n)))
    P=sum(v*v for v in c.values()); f=math.factorial(n)
    d=P/f
    print(n,'pairs',P,'d_n',d,'d_n^(1/n)',d**(1/n),'ratio',(d/prev if prev else None),'maxfiber',max(c.values()),'images',len(c),flush=True)
    prev=d
