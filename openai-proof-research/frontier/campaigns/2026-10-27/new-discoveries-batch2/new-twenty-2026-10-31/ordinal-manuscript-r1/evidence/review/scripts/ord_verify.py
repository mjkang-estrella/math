# Reviewer independent verification for MathDB 366371 witness.
import itertools,json,sys
from fractions import Fraction
rank=['23','34','12','24','01','13','14','45','35','02','25','03','04','15','05']
D=[[0]*6 for _ in range(6)]
for v,p in enumerate(rank,1):
    a,b=int(p[0]),int(p[1]);D[a][b]=D[b][a]=v
# matrix as in Lean file
LEAN=[[0,5,10,12,13,15],[5,0,3,6,7,14],[10,3,0,1,4,11],[12,6,1,0,2,9],[13,7,4,2,0,8],[15,14,11,9,8,0]]
assert D==LEAN,'ranking != Lean matrix'
X=range(6)
def cmp(a,b): return (a>b)-(a<b)
delta=lambda x,y,z,w: cmp(D[x][y],D[z][w])
# (1) ordinal-space axioms (i)-(vii), literal brute force
for x,y,z,w in itertools.product(X,repeat=4):
    assert delta(x,y,x,y)==0
    assert delta(x,y,z,w)==delta(y,x,z,w)==delta(x,y,w,z)
    assert delta(x,y,z,w)==-delta(z,w,x,y)
    assert delta(x,x,z,w)==(-1 if z!=w else 0)
for x,y,u,v,z,w in itertools.product(X,repeat=6):
    a,b,c=delta(x,y,u,v),delta(u,v,z,w),delta(x,y,z,w)
    if a==0 and b==0: assert c==0
    if a==-1 and b<=0: assert c==-1
    if a<=0 and b==-1: assert c==-1
print('ordinal axioms (i)-(vii): OK')
def mono(k): return [t for t in itertools.product(X,repeat=k+1) if all(t[i]<=t[i+1] for i in range(k))]
def pieces(t): return [D[t[i]][t[i+1]] for i in range(len(t)-1)]
# (2) literal Definition 7.1 with explicit permutations, k=1..4
lit={}
for k in range(1,5):
    T=mono(k);P=list(itertools.permutations(range(k)));viol=0;nprec=nsim=0;agree=0
    for I in T:
        f=pieces(I)
        for J in T:
            g=pieces(J)
            prec=any(all(f[l]<=g[p[l]] for l in range(k)) and not all(f[l]==g[p[l]] for l in range(k)) for p in P)
            sim=any(all(f[l]==g[p[l]] for l in range(k)) for p in P)
            # alternative reading of 'but not (7.4)': dominated via some pi and NOT sim
            prec_alt=any(all(f[l]<=g[p[l]] for l in range(k)) for p in P) and not sim
            sd=sorted(f);sg=sorted(g)
            prec_sorted=all(a<=b for a,b in zip(sd,sg)) and sd!=sg
            assert prec==prec_alt==prec_sorted and sim==(sd==sg)
            e=cmp(D[I[0]][I[-1]],D[J[0]][J[-1]])
            if prec: nprec+=1; viol+= e!=-1
            if sim: nsim+=1; viol+= e!=0
    lit[k]=dict(tuples=len(T),pairs=len(T)**2,prec_pairs=nprec,sim_pairs=nsim,violations=viol)
    print('literal k',k,lit[k],flush=True)
# (3) exact all-k characterization: chain = reduced strictly increasing list + zero pieces;
#     prec/sim depend only on padded sorted multisets, padding with zeros is dominance-invariant,
#     so checking each pair of reduced lists at k=max(#pieces,1) covers every k.
red=[c for r in range(1,7) for c in itertools.combinations(X,r)]
viol=0;cnt=0;thr_agree=True
for A in red:
    for B in red:
        k=max(len(A)-1,len(B)-1,1)
        f=sorted(pieces(A)+[0]*(k-len(A)+1));g=sorted(pieces(B)+[0]*(k-len(B)+1))
        prec=all(a<=b for a,b in zip(f,g)) and f!=g; sim=f==g
        # threshold counts as in the lane's okB
        cA=[sum(v>=t for v in pieces(A)) for t in range(1,16)];cB=[sum(v>=t for v in pieces(B)) for t in range(1,16)]
        tprec=all(a<=b for a,b in zip(cA,cB)) and cA!=cB; tsim=cA==cB
        thr_agree&= (tprec==prec and tsim==sim)
        e=cmp(D[A[0]][A[-1]],D[B[0]][B[-1]])
        if prec: viol+=e!=-1
        if sim: viol+=e!=0
        cnt+=1
print('all-k reduced pairs',cnt,'violations',viol,'threshold==sorted-dominance',thr_agree)
# (4) non-embeddability certificate
order_ok=all(D[0][x]<D[0][5] and D[x][5]<D[0][5] for x in (1,2,3,4)) and D[0][1]<D[0][2]<D[0][3]<D[0][4]
cert=[((2,3),(3,4)),((1,2),(2,4)),((0,1),(1,3)),((1,4),(4,5)),((3,5),(0,2))]
lhs=[0]*6;rhs=[0]*6
for (a,b),(c,d) in cert:
    assert D[a][b]<D[c][d]
    for i in range(a+1,b+1): lhs[i]+=1
    for i in range(c+1,d+1): rhs[i]+=1
print('forced order 0<1<2<3<4<5 (up to reflection):',order_ok,'gap coefficients lhs',lhs[1:],'rhs',rhs[1:],'identical:',lhs==rhs)
# (5) sanity: Prop 7.2 (ii) consequences
print('Prop7.2(ii):',[D[0][j] for j in range(1,6)],[D[i][5] for i in range(5)])
json.dump(dict(literal=lit,allk_pairs=cnt,allk_violations=viol,threshold_equiv=thr_agree,order_forced=order_ok,certificate_cancels=lhs==rhs),open(sys.argv[1],'w'),indent=1)
