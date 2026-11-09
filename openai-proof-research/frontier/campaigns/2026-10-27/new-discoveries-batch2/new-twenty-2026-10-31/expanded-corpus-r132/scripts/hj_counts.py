# Count-based search for 2-colourings of [k]^n (n=k-1 by default) with no red full
# combinatorial line and no blue 2-line (consecutive letters a,a+1).
# A colouring depending only on the letter-count vector N is valid iff B (blue count vectors)
#  (P) no two blue vectors differ by moving d>=1 units from letter a to a+1, and
#  (S) for every c with |c|=n-d (1<=d<=n) some c+d*e_j is blue.
import sys,itertools,time,json,random
def comps(n,k):
    if k==1: yield (n,); return
    for i in range(n+1):
        for r in comps(n-i,k-1): yield (i,)+r
def build(k,n):
    V=list(comps(n,k)); idx={v:i for i,v in enumerate(V)}
    pairs=[]  # cliques
    for a in range(k-1):
        groups={}
        for v in V:
            key=v[:a]+v[a+2:]
            groups.setdefault(key,[]).append(idx[v])
        for g in groups.values():
            if len(g)>1: pairs.append(g)
    stars=[]
    for d in range(1,n+1):
        for c in comps(n-d,k):
            s=[]
            for j in range(k):
                w=list(c); w[j]+=d; s.append(idx[tuple(w)])
            stars.append(sorted(set(s)))
    return V,idx,pairs,stars
def solve(k,n,limit_sec,seed=0,want_all=False):
    V,idx,cliques,stars=build(k,n)
    N=len(V)
    conf=[set() for _ in range(N)]
    for g in cliques:
        for x in g:
            conf[x].update(y for y in g if y!=x)
    starsof=[[] for _ in range(N)]
    for si,s in enumerate(stars):
        for x in s: starsof[x].append(si)
    state=[0]*N  # 0 undecided, 1 blue, -1 red
    t0=time.time(); sols=[]; nodes=[0]
    rnd=random.Random(seed)
    order_key=[rnd.random() for _ in range(N)]
    def propagate(assign_stack,x,val):
        # returns False on conflict
        todo=[(x,val)]
        while todo:
            y,v=todo.pop()
            if state[y]!=0:
                if state[y]!=v: return False
                continue
            state[y]=v; assign_stack.append(y)
            if v==1:
                for z in conf[y]:
                    if state[z]==1: return False
                    if state[z]==0: todo.append((z,-1))
            else:
                for si in starsof[y]:
                    s=stars[si]
                    if any(state[z]==1 for z in s): continue
                    und=[z for z in s if state[z]==0]
                    if not und: return False
                    if len(und)==1: todo.append((und[0],1))
        return True
    def undo(stack,mark):
        while len(stack)>mark: state[stack.pop()]=0
    stack=[]
    def pick():
        best=None;bl=10**9
        for s in stars:
            if any(state[z]==1 for z in s): continue
            und=[z for z in s if state[z]==0]
            if len(und)<bl: bl=len(und);best=und
            if bl<=1: break
        return best
    timed_out=[False]
    def dfs():
        nodes[0]+=1
        if time.time()-t0>limit_sec: timed_out[0]=True; return True
        und=pick()
        if und is None:
            sols.append([V[i] for i in range(N) if state[i]==1]); return not want_all
        und.sort(key=lambda z:order_key[z])
        for x in und:
            mark=len(stack)
            if propagate(stack,x,1):
                if dfs(): return True
            undo(stack,mark)
            # then x is red for remaining branches
            if not propagate(stack,x,-1):
                undo(stack,mark); return False
        return False
    dfs()
    return dict(k=k,n=n,vectors=N,cliques=len(cliques),stars=len(stars),nodes=nodes[0],timed_out=timed_out[0],nsol=len(sols),sol=sols[0] if sols else None,secs=time.time()-t0)
if __name__=='__main__':
    k=int(sys.argv[1]); n=int(sys.argv[2]) if len(sys.argv)>2 else k-1; lim=float(sys.argv[3]) if len(sys.argv)>3 else 100
    seed=int(sys.argv[4]) if len(sys.argv)>4 else 0
    r=solve(k,n,lim,seed)
    print(json.dumps(r))
