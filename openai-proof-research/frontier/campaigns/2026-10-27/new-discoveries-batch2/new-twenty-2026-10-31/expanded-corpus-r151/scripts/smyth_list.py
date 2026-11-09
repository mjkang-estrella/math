import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth_fast import flow_check
sys.setrecursionlimit(1000000)
t0=time.time()
for part in sys.argv[1].split(','):
    A,B,g,b0,b1=map(int,part.split(':'))
    for b in range(b0,b1+1):
        if time.time()-t0>float(sys.argv[2]): print('TIMEOUT',part,b); break
        nx,ny,f=flow_check(A,b+g,B,b)
        print(A,b+g,B,b,'|X|',nx,'|Y|',ny,'flow',f,'deficiency',nx-f,flush=True)
