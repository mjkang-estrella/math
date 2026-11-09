# Ground truth: all 7-smooth n < 10^DMAX (incl. factor 5) whose Pi-chain ends in a NONZERO digit,
# grouped by level (number of steps to the single digit). Independent of any family enumeration.
import sys
from math import prod
from multiprocessing import Pool
DMAX=int(sys.argv[1]); LIM=10**DMAX
def chain(n):
    lv=0
    while n>=10:
        s=str(n)
        if '0' in s: return None
        n=prod(map(int,s)); lv+=1
    return (lv,n) if n else None
def job(args):
    p,e=args; out=[]
    x=p**e
    y=x
    while y<LIM:
        z=y
        while z<LIM:
            if '0' not in str(z):
                c=chain(z)
                if c and c[0]>=1: out.append((c[0],z))
            z*=7
        y*=3
    return out
if __name__=='__main__':
    jobs=[(2,a) for a in range(int(DMAX*3.33)+2)]+[(5,c) for c in range(1,int(DMAX*1.44)+2)]
    res={}
    with Pool(8) as P:
        for out in P.imap_unordered(job,jobs):
            for lv,z in out: res.setdefault(lv,[]).append(z)
    for lv in sorted(res):
        v=sorted(res[lv]); print(f"level {lv}: {len(v)} members; largest {v[-1]} ({len(str(v[-1]))} digits)")
        if lv<=2: print("   ", v)
