# Local insertion game for complete bifurcate trees (356145).
# State: word over {0..k-1} with fixed end delimiters. Spoiler picks an interior gap,
# Builder picks a letter keeping the word square-free. Spoiler wins at depth d if
# some gap forces (within d more insertions) a square for every Builder answer.
# A Spoiler win from the two-letter word "01" excludes every complete bifurcate tree
# whose root has length >= 1 (any adjacent pair of distinct letters is such a window).
import sys,time
k=int(sys.argv[1]); maxd=int(sys.argv[2]); start=tuple(int(c) for c in (sys.argv[3] if len(sys.argv)>3 else '01'))
def newsquare(w,p):
    # does w contain a square through position p (w square-free before insertion at p)?
    n=len(w)
    for L in range(1,n//2+1):
        lo=max(0,p-2*L+1); hi=min(p,n-2*L)
        for s in range(lo,hi+1):
            if w[s:s+L]==w[s+L:s+2*L]: return True
    return False
def canon(w):
    best=None
    for v in (w,w[::-1]):
        m={};out=[]
        for c in v:
            if c not in m: m[c]=len(m)
            out.append(m[c])
        t=tuple(out)
        if best is None or t<best: best=t
    return best
memo={}  # canon -> max depth d known Builder survives (as negative) or Spoiler win depth
nodes=0
def spoiler_wins(w,d):
    # True if Spoiler forces a square within d insertions
    global nodes
    if d==0: return False
    c=canon(w)
    r=memo.get(c)
    if r is not None:
        if r>0 and r<=d: return True      # spoiler wins within r<=d
        if r<0 and -r>=d: return False    # builder survives at least -r>=d
    nodes+=1
    res=False
    for p in range(1,len(w)):
        ok=True
        for x in range(k):
            w2=w[:p]+(x,)+w[p:]
            if newsquare(w2,p): continue
            if not spoiler_wins(w2,d-1): ok=False;break
        if ok: res=True;break
    if res:
        memo[c]=d if (c not in memo or memo[c]<0 or memo[c]>d) else memo[c]
    else:
        memo[c]=-d if (c not in memo or memo[c]>0 or -memo[c]<d) else memo[c]
    return res
t=time.time()
for d in range(1,maxd+1):
    r=spoiler_wins(start,d)
    print(f"k={k} start={''.join(map(str,start))} depth={d} spoiler_wins={r} nodes={nodes} memo={len(memo)} t={time.time()-t:.1f}",flush=True)
    if r: break
