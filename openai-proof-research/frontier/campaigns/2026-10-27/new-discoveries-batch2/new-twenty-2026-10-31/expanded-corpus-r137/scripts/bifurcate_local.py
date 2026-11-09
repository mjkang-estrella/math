# Restricted-Spoiler variant of bifurcate.py: after the first move, Spoiler may only insert
# at gaps within distance r of the last inserted letter. A Spoiler win here is still a Spoiler
# win in the unrestricted game (restriction only weakens Spoiler).
import sys,time
k=int(sys.argv[1]); maxd=int(sys.argv[2]); r=int(sys.argv[3]); start=tuple(int(c) for c in (sys.argv[4] if len(sys.argv)>4 else '01'))
def newsquare(w,p):
    n=len(w)
    for L in range(1,n//2+1):
        lo=max(0,p-2*L+1); hi=min(p,n-2*L)
        for s in range(lo,hi+1):
            if w[s:s+L]==w[s+L:s+2*L]: return True
    return False
def canon(w,q):
    m={};out=[]
    for c in w:
        if c not in m: m[c]=len(m)
        out.append(m[c])
    a=(tuple(out),q)
    v=w[::-1]; m={};out=[]
    for c in v:
        if c not in m: m[c]=len(m)
        out.append(m[c])
    b=(tuple(out),len(w)-1-q if q is not None else None)
    return min(a,b,key=lambda t:(t[0],-1 if t[1] is None else t[1]))
memo={}; nodes=0
def gaps(w,q):
    if q is None: return range(1,len(w))
    return [g for g in range(max(1,q-r+1),min(len(w)-1,q+r)+1)]
def spoiler_wins(w,q,d):
    global nodes
    if d==0: return False
    c=canon(w,q); m=memo.get(c)
    if m is not None:
        if m>0 and m<=d: return True
        if m<0 and -m>=d: return False
    nodes+=1; res=False
    for p in gaps(w,q):
        ok=True
        for x in range(k):
            w2=w[:p]+(x,)+w[p:]
            if newsquare(w2,p): continue
            if not spoiler_wins(w2,p,d-1): ok=False;break
        if ok: res=True;break
    if res: memo[c]=d if (m is None or m<0 or m>d) else m
    else: memo[c]=-d if (m is None or m>0 or -m<d) else m
    return res
t=time.time()
for d in range(1,maxd+1):
    res=spoiler_wins(start,None,d)
    print(f"k={k} r={r} depth={d} spoiler_wins={res} nodes={nodes} memo={len(memo)} t={time.time()-t:.1f}",flush=True)
    if res: break
