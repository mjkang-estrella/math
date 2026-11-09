# Scan all (a,b) with b<a, a+b<=nmax for given (A,B); report failures.
import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth_fast import flow_check
sys.setrecursionlimit(1000000)
t0=time.time()
for part in sys.argv[1].split(','):
    A,B,n0,n1=map(int,part.split(':')); fails=[]; done=None
    for n in range(n0,n1+1):
        if time.time()-t0>float(sys.argv[2]): print('TIMEOUT',A,B,'at n',n,flush=True); break
        for b in range(0,(n+1)//2):
            a=n-b
            nx,ny,f=flow_check(A,a,B,b)
            if f<nx: fails.append((a,b,nx-f))
        done=n
    print('A',A,'B',B,'n range',n0,'..',done,'failures',fails[:12],'count',len(fails),'t',round(time.time()-t0,1),flush=True)
