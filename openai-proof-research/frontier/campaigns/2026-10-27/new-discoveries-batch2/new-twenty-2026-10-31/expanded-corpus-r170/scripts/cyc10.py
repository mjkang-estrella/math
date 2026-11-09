import sys,time,gzip,os
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
from cyc import has_cyc,tri_free
start=int(sys.argv[1]);cnt=int(sys.argv[2]); n=10
t0=time.time(); tested=0; to=0; hits=0; last=start
with gzip.open('sources/graphdata/graph10c.g6.gz','rt') as f:
    for idx,line in enumerate(f):
        if idx<start: continue
        if idx>=start+cnt: break
        last=idx
        adj=parse(line); m=sum(map(len,adj))//2; D=max(map(len,adj))
        if D<5 or m<=n or not tri_free(adj): continue
        tmax=min(m,n+D-3)
        if tmax<=n: continue
        tested+=1
        for t in range(n+1,tmax+1):
            try:
                if has_cyc(adj,t): hits+=1; print('HIT',idx,line.strip(),'t',t,flush=True); break
            except TimeoutError: to+=1; print('TO',idx,line.strip(),t,flush=True)
        if time.time()-t0>112: print('timecap at',idx); break
print('n10 i',start,last,'tested',tested,'timeouts',to,'hits',hits,round(time.time()-t0,1))
