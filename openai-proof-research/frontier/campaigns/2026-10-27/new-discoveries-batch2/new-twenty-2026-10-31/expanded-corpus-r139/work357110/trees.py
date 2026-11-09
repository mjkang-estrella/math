# 357110: exhaustive search over free trees (Wright-Richmond-Odlyzko-McKay generation) of odd order n,
# domination number (n-1)/2, minimizing spectral radius. Pure python, exact gamma by tree DP,
# spectral radius by power iteration on A+I (bipartite safe) to 1e-13, then ties re-checked.
import sys, math, json
def free_trees(n):
    # WROM: level sequences; yields parent arrays
    if n==1: yield [-1]; return
    if n==2: yield [-1,0]; return
    k=n//2+1
    L=list(range(k))+list(range(1,n-k+1))
    W=[i-1 for i in range(k)]+[0]+list(range(k,n-1))
    # standard implementation adapted from networkx nonisomorphic_trees
    p=k-1 if n-k+1<=1 else n-1
    # use networkx-style generator
    yield from _nx(n)
def _nx(order):
    layout=list(range(order//2+1))+list(range(1,(order+1)//2))
    while layout is not None:
        yield _parents(layout)
        layout=_next_tree(_next_rooted_tree(layout))
def _next_rooted_tree(predecessor,p=None):
    if p is None:
        p=len(predecessor)-1
        while predecessor[p]==1: p-=1
    if p==0: return None
    q=p-1
    while predecessor[q]!=predecessor[p]-1: q-=1
    result=list(predecessor)
    for i in range(p,len(result)):
        result[i]=result[i-p+q]
    return result
def _next_tree(candidate):
    if candidate is None: return None
    left,rest=_split_tree(candidate)
    left_height=max(left); rest_height=max(rest)
    valid=rest_height>=left_height
    if valid and rest_height==left_height:
        if len(left)>len(rest): valid=False
        elif len(left)==len(rest) and left>rest: valid=False
    if valid: return candidate
    p=len(left)
    new_candidate=_next_rooted_tree(candidate,p)
    if candidate[p]>2:
        new_left,new_rest=_split_tree(new_candidate)
        new_left_height=max(new_left)
        suffix=range(1,new_left_height+2)
        new_candidate[-len(suffix):]=suffix
    return new_candidate
def _split_tree(layout):
    one_found=False; m=None
    for i in range(len(layout)):
        if layout[i]==1:
            if one_found: m=i; break
            else: one_found=True
    if m is None: m=len(layout)
    left=[layout[i]-1 for i in range(1,m)]
    rest=[0]+[layout[i] for i in range(m,len(layout))]
    return (left,rest)
def _parents(layout):
    par=[-1]*len(layout); stack=[]
    for i,d in enumerate(layout):
        while stack and layout[stack[-1]]>=d: stack.pop()
        par[i]=stack[-1] if stack else -1
        stack.append(i)
    return par
def adj_of(par):
    n=len(par); adj=[[] for _ in range(n)]
    for i,p in enumerate(par):
        if p>=0: adj[i].append(p); adj[p].append(i)
    return adj
def gamma_tree(adj):
    n=len(adj); INF=10**9
    order=[];seen=[False]*n;st=[0];seen[0]=True;par=[-1]*n
    while st:
        v=st.pop();order.append(v)
        for w in adj[v]:
            if not seen[w]: seen[w]=True;par[w]=v;st.append(w)
    # states: a=v in D; b=v not in D, dominated by child; c=v not in D, not dominated yet (needs parent)
    A=[0]*n;B=[0]*n;C=[0]*n
    for v in reversed(order):
        ch=[w for w in adj[v] if w!=par[v]]
        a=1+sum(min(A[w],B[w],C[w]) for w in ch)
        c=sum(B[w] for w in ch) if ch else 0
        if ch:
            base=sum(min(A[w],B[w]) for w in ch)
            extra=min(max(0,A[w]-B[w]) for w in ch)
            b=base+extra
        else: b=INF
        A[v],B[v],C[v]=a,min(b,INF),min(c,INF)
    return min(A[0],B[0])
def rho(adj,it=200000,tol=1e-14):
    n=len(adj); x=[1.0]*n; lam=0
    for t in range(it):
        y=[x[i]+sum(x[j] for j in adj[i]) for i in range(n)]
        s=max(y); y=[v/s for v in y]
        if t>20 and abs(s-lam)<tol: break
        lam=s; x=y
    return lam-1
def comb_sub(k):
    # H': path v1..vk with leaves l_i, pendant edge v1-l1 subdivided
    n=2*k+1; adj=[[] for _ in range(n)]
    def e(a,b): adj[a].append(b); adj[b].append(a)
    for i in range(k-1): e(i,i+1)
    for i in range(1,k): e(i,k+i)
    e(0,2*k); e(2*k,k)  # v1 - s - l1 with s=2k, l1=k
    return adj
if __name__=='__main__':
    n=int(sys.argv[1]); g=(n-1)//2
    H=comb_sub(g); assert gamma_tree(H)==g; rH=rho(H)
    res=[];cnt=0;cntg=0
    for par in _nx(n):
        cnt+=1; adj=adj_of(par)
        if gamma_tree(adj)!=g: continue
        cntg+=1; r=rho(adj); res.append((r,sorted(len(a) for a in adj),par))
    res.sort()
    print(json.dumps({'n':n,'trees':cnt,'trees_gamma':cntg,'rho_Hprime':rH,
      'best':[(r,d,p) for r,d,p in res[:4]],'n_below_or_equal_H':sum(1 for r,_,_ in res if r<=rH+1e-9)}))
