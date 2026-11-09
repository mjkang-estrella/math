# 331313 / Csoka-Lo-Norin-Wu-Yepremyan Conjecture 12 exact staircase check on all graphs from a g6 file.
import sys,json
sys.path.insert(0,sys.argv[1]); import g6
from fractions import Fraction as F
path=sys.argv[2]; start=int(sys.argv[3]); count=None if sys.argv[4]=='all' else int(sys.argv[4])
worst=[]; tot=0; viol=[]
for k,line in g6.stream(path,start,count):
    n,adj=g6.parse(line); tot+=1
    E=sum(bin(a).count('1') for a in adj)//2
    if E<n+1: continue   # need d=E/n >1 for a nontrivial interior segment
    full=(1<<n)-1
    e=[0]*(1<<n)
    for S in range(1,1<<n):
        b=S&-S; v=b.bit_length()-1; R=S^b
        e[S]=e[R]+bin(adj[v]&R).count('1')
    pc=[bin(S).count('1') for S in range(1<<n)]
    # pairs (d1,d2); by symmetry consider all S nonempty proper
    best={}  # d1 -> max d2
    for S in range(1,full):
        d1=F(e[S],pc[S]); T=full^S; d2=F(e[T],pc[T])
        if best.get(d1,-1)<d2: best[d1]=d2
    d=F(E,n)
    keys=sorted(best)
    # suffix max of d2 over d1 > a
    suf=[None]*len(keys); m=F(-1)
    for i in range(len(keys)-1,-1,-1):
        suf[i]=m; m=max(m,best[keys[i]])
    slack=m-(d-1)  # s=0 check uses max over all
    wa=None
    if slack<0: wa=('s0',slack)
    for i,a in enumerate(keys):
        if a>=d-1: break
        if suf[i] is None or suf[i]<0: sl=-(d-1-a)
        else: sl=suf[i]-(d-1-a)
        if sl<slack: slack=sl; wa=(str(a),str(sl))
    if slack<0: viol.append((line.strip(),str(d),wa))
    worst.append((slack,line.strip()))
worst.sort()
print(json.dumps({'file':path,'count':tot,'violations':viol[:50],'nviol':len(viol),'min_slack':[(str(s),g) for s,g in worst[:8]]}))
