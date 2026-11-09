"""Independent exact diagnostics; not a proof or a formal certificate."""
from fractions import Fraction as Q
from itertools import product, combinations_with_replacement
from pathlib import Path
import random, json, datetime
O=Path(__file__).resolve().parent
def flow(rank, scores, a):
    n=len(rank); m=len(scores); S=sum(scores)
    q=[sum(scores[r.index(c)] for r in rank)/(n*S) for c in range(m)]
    N=n+m+2; t=N-1; cap=[[Q(0) for _ in range(N)] for _ in range(N)]
    for i,r in enumerate(rank):
        cap[0][i+1]=Q(1,n)
        for c in r[r.index(a):]:cap[i+1][n+1+c]=Q(1)
    for c in range(m):cap[n+1+c][t]=q[c]
    total=Q(0)
    while True:
        prev={0:None}; todo=[0]
        for u in todo:
            for v in range(N):
                if cap[u][v]>0 and v not in prev:prev[v]=u;todo.append(v)
        if t not in prev:break
        v=t; aug=Q(1)
        while v: u=prev[v];aug=min(aug,cap[u][v]);v=u
        v=t
        while v:u=prev[v];cap[u][v]-=aug;cap[v][u]+=aug;v=u
        total+=aug
    if total!=1:return None
    return q,[[cap[n+1+c][i+1] for c in range(m)] for i in range(n)]
def run():
    scalar=0
    for m in range(2,6):
        for tail in combinations_with_replacement([Q(k,4) for k in range(5)],m-1):
            s=[Q(1)]+list(reversed(tail));S=sum(s);v=s[-1];T=S-v;mu=1/S
            for p in [Q(k,80) for k in range(81)]:
                floor=(p+v*(1-p))/S
                for q in {floor,Q(1)-p,(floor+1-p)/2}:
                    if not floor<=q<=1-p:continue
                    K=mu*(1-p)+q
                    if K>1:continue  # remaining columns must cover non-b plurality tokens
                    assert p<=T/(T+1) and 0<K<=1
                    assert (T+1)*K>=1+mu
                    assert 2*mu+2*(1-K)*(1+mu)/K<=2*T
                    scalar+=1
    rng=random.Random(40265);cases=0;comparisons=0;zeroR=0;zeroD=0
    for z in range(1600):
        m=rng.randrange(2,6);n=rng.randrange(1,7)
        s=[Q(1)]+sorted([Q(rng.randrange(5),4) for _ in range(m-1)],reverse=True)
        cv=[rng.randrange(-3,4) for _ in range(m)];vv=[rng.randrange(-3,4) for _ in range(n)]
        rank=[sorted(range(m),key=lambda c:(abs(x-cv[c]),c)) for x in vv]
        for a in range(m):
            f=flow(rank,s,a)
            if f is None:continue
            qv,W=f;cases+=1
            for b in range(m):
                if a==b:continue
                S=sum(s);mu=1/S;T=S-s[-1];q=qv[b]
                F=[i for i,r in enumerate(rank) if r[0]==b];p=Q(len(F),n)
                assert all(W[i][b]==0 for i in F)
                assert p+q<=1
                K=mu*(1-p)+q
                r=[Q(abs(x-cv[b])) for x in vv];D=Q(abs(cv[a]-cv[b]));R=sum(r)/n
                H=sum(r[i] for i in F)/n;E=sum(Q(abs(x-cv[a]))-ri for x,ri in zip(vv,r))/n
                # Independently instantiate every arc and the exact column splitting.
                incoming=[Q(0)]*n;special=Q(0);good=Q(0)
                for i in range(n):
                    special+=W[i][b]
                    for j in range(n):
                        c=rank[j][0]
                        if c==b:continue
                        g=W[i][c]*mu/(n*qv[c]);incoming[j]+=g;good+=g
                        if g:
                            xi=Q(abs(vv[i]-cv[a]))
                            assert xi<=r[i]+2*r[j] and D<=2*(r[i]+r[j])
                assert incoming==[Q(0) if j in F else mu/n for j in range(n)]
                assert good+special==K
                assert E<=2*mu*(R-H)+(1-K)*D
                assert K*D<=2*((1+mu)*R-mu*H)
                assert E<=2*T*R
                zeroR+=R==0;zeroD+=D==0;comparisons+=1
    return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scalar_exact_cases':scalar,'line_metric_core_members':cases,'pair_comparisons':comparisons,'zero_R_cases':zeroR,'zero_D_cases':zeroD,'failures':[],'limits':'Exact fractions; finite diagnostics, line pseudometrics only; full proof is review.md.'}
if __name__=='__main__':
    result=run();(O/'check-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
