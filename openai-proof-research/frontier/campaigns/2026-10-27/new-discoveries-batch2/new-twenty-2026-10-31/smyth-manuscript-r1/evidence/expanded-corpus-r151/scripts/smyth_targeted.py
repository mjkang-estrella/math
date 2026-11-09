import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth import check
spec=sys.argv[1]  # list of B:Amin:Amax:nmin:nmax
t0=time.time();cnt=0
for part in spec.split(','):
  B,A0,A1,n0,n1=map(int,part.split(':'))
  for A in range(A0,A1+1):
    for n in range(n0,n1+1):
      for b in range(0,n//2+1):
        a=n-b
        if a==b: continue
        nx,ny,f=check(A,a,B,b); cnt+=1
        if f<nx: print('FAIL',A,a,B,b,nx,ny,f,flush=True)
      print('done A',A,'B',B,'n',n,'t',round(time.time()-t0,1),flush=True)
print('checked',cnt)
