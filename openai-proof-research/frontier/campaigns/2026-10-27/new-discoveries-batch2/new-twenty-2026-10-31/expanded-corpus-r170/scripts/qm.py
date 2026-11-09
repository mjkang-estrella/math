# Exhaustive: does connected graph G (nice) admit a quasi-majority neighbor-sum-distinguishing k-edge-colouring?
import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
def qm_nsd(adj,k):
    n=len(adj); deg=[len(a) for a in adj]
    # edge order: BFS-ish so vertices complete early
    order=sorted(range(n),key=lambda v:-deg[v])
    seen=set();edges=[]
    pos={}
    for v in order:
        for w in adj[v]:
            e=(min(v,w),max(v,w))
            if e not in seen: seen.add(e);edges.append(e)
    m=len(edges)
    last={}  # vertex -> index of its last edge
    for i,(a,b) in enumerate(edges): last[a]=i; last[b]=i
    cap=[(d+1)//2 for d in deg]
    cnt=[[0]*(k+1) for _ in range(n)]; s=[0]*n
    done_at={}
    for v,i in last.items(): done_at.setdefault(i,[]).append(v)
    def ok_done(i):
        for v in done_at.get(i,()):
            for w in adj[v]:
                if last[w]<=i and s[w]==s[v]: return False
        return True
    def rec(i):
        if i==m: return True
        a,b=edges[i]
        for c in range(1,k+1):
            if cnt[a][c]>=cap[a] or cnt[b][c]>=cap[b]: continue
            if i==0 and c>(k+1)//2+1: continue
            cnt[a][c]+=1;cnt[b][c]+=1;s[a]+=c;s[b]+=c
            if ok_done(i) and rec(i+1):
                return True
            cnt[a][c]-=1;cnt[b][c]-=1;s[a]-=c;s[b]-=c
        return False
    return rec(0)
if __name__=='__main__':
    n=int(sys.argv[1]); start=int(sys.argv[2]); cntg=int(sys.argv[3]); mindeg=int(sys.argv[4]) if len(sys.argv)>4 else 4
    lines=open(f'sources/graphdata/graph{n}c.g6').read().split()
    t=time.time(); tested=0; bad=[]
    for idx in range(start,min(len(lines),start+cntg)):
        adj=parse(lines[idx])
        if max(len(a) for a in adj)<mindeg: continue
        tested+=1
        if not qm_nsd(adj,4): bad.append(lines[idx]); print('NO4',idx,lines[idx],flush=True)
    print('n',n,'range',start,start+cntg,'of',len(lines),'tested',tested,'bad',len(bad),'secs',round(time.time()-t,1))
