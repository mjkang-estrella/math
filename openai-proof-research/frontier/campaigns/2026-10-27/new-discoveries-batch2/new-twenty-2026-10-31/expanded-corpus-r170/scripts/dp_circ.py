import sys,time,itertools
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp import bfs_all,strong,solve
def circ(n,S): return [sorted({(i+s)%n for s in S}|{(i-s)%n for s in S}) for i in range(n)]
d,p,nmax,lim=map(int,sys.argv[1:5]); budget=float(sys.argv[5])
t0=time.time(); bad=[]; good=[]
for n in range(5,nmax+1):
    for a in range(2,n//2+1):
        if a==n-a: continue
        A=circ(n,[1,a]); D=bfs_all(A)
        if max(D[0])<p+1: continue
        r,_=solve(n,lambda x,y:D[x][y],d,p,first_fixed=0)
        (bad if r is None else good).append(('C%d(1,%d)'%(n,a),D))
print('bad',[b[0] for b in bad],flush=True)
cnt=0
for (gn,DG),(hn,DH) in itertools.combinations_with_replacement(bad+good[:15],2):
    if not any(gn==b[0] for b in bad) and not any(hn==b[0] for b in bad): continue
    N,dist=strong(DG,DH)
    if N>1600: continue
    try: r,nodes=solve(N,dist,d,p,first_fixed=0,limit=lim)
    except TimeoutError: print('TO',gn,hn,flush=True); continue
    cnt+=1
    if r: print('FOUND',gn,hn,r,flush=True)
    if time.time()-t0>budget: print('budget stop',cnt);sys.exit()
print('done',cnt)
