# Exact independence number of Cay(F_p^3, S), S = {(a^2,2ab,b^2)} u -S, p prime, via branch and bound.
# Bound: for each conic direction s, the cosets of span(s) partition vertices; each induces a circulant on F_p
# (t ~ t' iff (t-t') * s in S). bound = min over directions of sum over lines of alpha(line restricted).
import sys,itertools,time
p=int(sys.argv[1]); target=int(sys.argv[2]) if len(sys.argv)>2 else 0
sq={(x*x)%p for x in range(1,p)}
S=set()
for a in range(p):
    for b in range(p):
        if a or b:
            s=((a*a)%p,(2*a*b)%p,(b*b)%p); S.add(s); S.add(tuple((-c)%p for c in s))
verts=list(itertools.product(range(p),repeat=3)); idx={v:i for i,v in enumerate(verts)}; N=len(verts)
adj=[0]*N
for i,v in enumerate(verts):
    for s in S: adj[i]|=1<<idx[tuple((x+y)%p for x,y in zip(v,s))]
# conic directions (projective points)
dirs=[]; seen=set()
for a in range(p):
    for b in range(p):
        if a or b:
            s=((a*a)%p,(2*a*b)%p,(b*b)%p)
            key=min(tuple((c*t)%p for c in s) for t in range(1,p))
            if key not in seen: seen.add(key); dirs.append(s)
lines_by_dir=[]
for s in dirs:
    done=0; lines=[]
    for i,v in enumerate(verts):
        if done>>i&1: continue
        L=[idx[tuple((x+t*c)%p for x,c in zip(v,s))] for t in range(p)]
        for j in L: done|=1<<j
        lines.append(L)
    lines_by_dir.append(lines)
# alpha of induced subgraph on a line, by position mask: positions t,t' adjacent iff (t-t')s in S
def line_alpha_table(s):
    nb=[0]*p
    for t in range(p):
        for u in range(p):
            if t!=u and tuple(((t-u)*c)%p for c in s) in S: nb[t]|=1<<u
    tab=[0]*(1<<p)
    for m in range(1,1<<p):
        # alpha via recursion on lowest bit
        v=(m&-m).bit_length()-1
        rest=m&~(1<<v)
        tab[m]=max(tab[rest],1+tab[rest&~nb[v]])
    return tab
tabs=[line_alpha_table(s) for s in dirs]
linemasks=[]
for d,lines in enumerate(lines_by_dir):
    linemasks.append([(L) for L in lines])
def bound(R):
    best=10**9
    for d,lines in enumerate(lines_by_dir):
        tab=tabs[d]; tot=0
        for L in lines:
            m=0
            for t,j in enumerate(L):
                if R>>j&1: m|=1<<t
            if m: tot+=tab[m]
            if tot>=best: break
        if tot<best: best=tot
    return best
best=[target]; bestset=[0]; nodes=[0]; t0=time.time()
def rec(R,size,cur):
    nodes[0]+=1
    if R==0:
        if size>best[0]: best[0]=size; bestset[0]=cur; print('new best',size,round(time.time()-t0,1),flush=True)
        return
    if size+bin(R).count('1')<=best[0]: return
    if size+bound(R)<=best[0]: return
    # branch on vertex of max degree within R
    bv=-1;bd=-1
    r=R
    while r:
        x=r&-r; r^=x; v=x.bit_length()-1
        dd=bin(adj[v]&R).count('1')
        if dd>bd: bd=dd; bv=v
    if bd==0:
        rec(0,size+bin(R).count('1'),cur|R); return
    rec(R&~(1<<bv)&~adj[bv],size+1,cur|(1<<bv))
    rec(R&~(1<<bv),size,cur)
FULL=(1<<N)-1
# vertex transitivity: include vertex 0
rec(FULL&~1&~adj[0],1,1)
print('p',p,'alpha',best[0],'(target lower start',target,') nodes',nodes[0],'sec',round(time.time()-t0,1))
if bestset[0]: print('set',[verts[i] for i in range(N) if bestset[0]>>i&1])
