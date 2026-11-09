import sys,time,gzip
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
from qm import qm_nsd
n=int(sys.argv[1]); mode=sys.argv[2]; start=int(sys.argv[3]); cnt=int(sys.argv[4])
path=f'sources/graphdata/graph{n}c.g6'+('.gz' if n==10 else '')
op=gzip.open if n==10 else open
t=time.time(); tested=0; bad=0; last=start
with op(path,'rt') as f:
    for idx,line in enumerate(f):
        if idx<start: continue
        if idx>=start+cnt: break
        last=idx
        # fast degree computation from graph6 bits
        adj=parse(line); deg=[len(a) for a in adj]
        if mode=='reg' and (min(deg)!=max(deg) or deg[0]<4): continue
        if mode.startswith('mind') and (min(deg)<int(mode[4:]) or max(deg)<4): continue
        tested+=1
        if not qm_nsd(adj,4): bad+=1; print('NO4',idx,line.strip(),flush=True)
        if time.time()-t>115: print('timecap at',idx); break
print('n',n,mode,start,last,'tested',tested,'bad',bad,round(time.time()-t,1))
