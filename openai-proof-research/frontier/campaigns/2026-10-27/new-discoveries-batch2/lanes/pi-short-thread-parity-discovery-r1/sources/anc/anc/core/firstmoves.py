"""First-move table for a spider S(x,y,z) (markable leg lengths). Moves named leg letter + cell index from centre + direction
(T = toward centre, A = away)."""
import sys, decomp
xs=tuple(int(a) for a in sys.argv[1:])
n,edges=decomp.spider_edges(tuple(x+1 for x in xs))
names={}
idx=0
for li,x in enumerate(xs):
    for cell in range(1,x+2):
        names[idx]=("abcd"[li],cell)  # cell x+1 is pendant
        idx+=1
m=len(edges)
def pos(state):
    lab={v:'N' for v in range(n)}
    for i,s in enumerate(state):
        if s:
            u,v=edges[i]; t,h=(u,v) if s=='A' else (v,u)   # edges stored (inner,outer)
            lab[t]=decomp.OUT_AFTER[lab[t]]; lab[h]=decomp.IN_AFTER[lab[h]]
    return lab,[edges[i] for i in range(m) if not state[i]]
def legal(state,i,s):
    st=list(state); st[i]=s
    for w in edges[i]:
        inc=[k for k in range(m) if w in edges[k]]
        if all(st[k] for k in inc):
            heads=[(edges[k][1] if st[k]=='A' else edges[k][0]) for k in inc]
            if all(h==w for h in heads) or all(h!=w for h in heads): return False
    return True
def G(state): return decomp.grundy_position(*pos(state))
empty=[None]*m
print("S",xs,"G =",G(empty))
for i in range(m):
    for s in ('A','T'):
        if not legal(empty,i,s): continue
        st=list(empty); st[i]=s; g1=G(st)
        reps=[]
        for k in range(m):
            for t in ('A','T'):
                if st[k] is None and legal(st,k,t):
                    st2=list(st); st2[k]=t
                    if G(st2)==0: reps.append("%s%d%s"%(names[k][0],names[k][1],t))
        print("%s%d%s  value %d  replies %s"%(names[i][0],names[i][1],s,g1,", ".join(reps)))
