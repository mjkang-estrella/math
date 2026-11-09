import sys, time
from math import prod
from multiprocessing import Pool
DMAX=int(sys.argv[1]); LIM=10**DMAX
def P(n):
    k=0
    while n>=10:
        s=str(n)
        if '0' in s: return k+1
        n=prod(map(int,s)); k+=1
    return k
def job(arg):
    p,e=arg; x=p**e; hist={}; front=[]; pts=0
    if x>=LIM: return 0,{},[]
    y=x
    while y<LIM:
        z=y
        while z<LIM:
            pts+=1
            s=str(z)
            if '0' not in s:
                k=P(z); hist[k]=hist.get(k,0)+1
                if k>=10: front.append(z)
            z*=7
        y*=3
    return pts,hist,front
if __name__=='__main__':
    t0=time.time()
    jobs=[(2,a) for a in range(0,int(DMAX*3.33)+2)]+[(5,c) for c in range(1,int(DMAX*1.44)+2)]
    jobs.sort(key=lambda j: j[1] if j[0]==2 else j[1]*2.32)   # heavy jobs first-ish
    pts=0; H={}; F=set()
    with Pool(30) as pool:
        for p,h,f in pool.imap_unordered(job,jobs):
            pts+=p; F.update(f)
            for k,v in h.items(): H[k]=H.get(k,0)+v
    print(f"DMAX={DMAX} points={pts} zero-free hist={dict(sorted(H.items()))}")
    print(f"P>=10: {sorted(F)}  max P = {max(H)}  {time.time()-t0:.0f}s")
