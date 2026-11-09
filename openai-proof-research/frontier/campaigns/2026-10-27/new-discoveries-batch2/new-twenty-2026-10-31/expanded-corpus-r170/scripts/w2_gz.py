import sys,time,gzip
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
from w2 import wc,cond2,w2
start=int(sys.argv[1]);cnt=int(sys.argv[2])
t=time.time(); stats=dict(tested=0,notwc=0,c2=0,w2=0,mismatch=0)
with gzip.open('sources/graphdata/graph10c.g6.gz','rt') as f:
    for idx,line in enumerate(f):
        if idx<start: continue
        if idx>=start+cnt: break
        adj=parse(line); n=len(adj); nb=[sum(1<<w for w in a) for a in adj]
        stats['tested']+=1
        iswc,Ms=wc(n,nb,(1<<n)-1)
        c2=cond2(n,nb,Ms)
        if c2: stats['c2']+=1
        if not iswc: stats['notwc']+=1
        W=w2(n,nb) if iswc else False
        if W: stats['w2']+=1
        if W!=c2: stats['mismatch']+=1; print('MISMATCH',idx,line.strip(),iswc,W,c2,flush=True)
print('n10',start,start+cnt,stats,round(time.time()-t,1),flush=True)
