# For given (A,B) and gap g=a-b, scan b upward and report first failure.
import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth import check
t0=time.time(); tl=float(sys.argv[2])
for part in sys.argv[1].split(','):
    A,B,g,bmax=map(int,part.split(':'))
    found=None
    for b in range(0,bmax+1):
        if time.time()-t0>tl: print('TIMEOUT at',A,B,g,b,flush=True); break
        a=b+g
        nx,ny,f=check(A,a,B,b)
        if f<nx: found=(A,a,B,b,nx,ny,f); break
    print('A',A,'B',B,'gap',g,'first failure',found,'scanned b<=',b,'t',round(time.time()-t0,1),flush=True)
