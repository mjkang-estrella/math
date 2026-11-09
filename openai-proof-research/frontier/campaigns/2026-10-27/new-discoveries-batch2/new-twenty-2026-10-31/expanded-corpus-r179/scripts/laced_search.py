import sys,random,itertools,math,runpy,time
sys.path.insert(0,'')  # not used
L=runpy.run_path(__file__.replace('laced_search.py','laced.py'))
analyse,best_interweaved=L['analyse'],L['best_interweaved']
n,k,seed,iters=map(int,sys.argv[1:5]); N=(n-1)*(n-2)//2+k
rnd=random.Random(seed); triples=list(itertools.combinations(range(N),3))
def cost(col):
    end,st,maxcap,maxcup,Ein,Sout=analyse(N,n,col)
    # violations: count edges carrying long caps / cups
    v=0
    for p in range(N):
        for x in range(p):
            pass
    capv=max(0,maxcap-3); cupv=max(0,maxcup-(n-1))
    if capv or cupv: return 100*(capv+cupv)+50,None
    b,_=best_interweaved(N,n,col,Ein,Sout); return b,b
best=None; t0=time.time(); found=0
restarts=0
while time.time()-t0<float(sys.argv[5]):
    col={t:rnd.randint(0,1) for t in triples}; c,_=cost(col); restarts+=1
    T=2.0
    for it in range(iters):
        t=rnd.choice(triples); col[t]^=1; c2,_=cost(col)
        if c2<=c or rnd.random()<math.exp((c-c2)/T): c=c2
        else: col[t]^=1
        T=max(0.05,T*0.995)
        if c<k: 
            print('COUNTEREXAMPLE n',n,'k',k,'N',N,'value',c,sorted(t for t in triples if col[t]==1)); found=1; break
    if best is None or c<best: best=c
    if found: break
print('n',n,'k',k,'N',N,'restarts',restarts,'best final cost',best,'time',round(time.time()-t0,1))
