"""Exact finite tests; standard library only. No file writes on import or execution."""
from fractions import Fraction as F
from itertools import combinations, product
from collections import defaultdict, Counter
from math import comb, prod
import json

def edge(a,b): return tuple(sorted((a,b)))
def identity(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def zero(n): return [[F(0) for _ in range(n)] for _ in range(n)]
def add(a,b): return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,c): return [[c*x for x in r] for r in a]
def mul(a,b):
    cols=list(zip(*b))
    return [[sum(x*y for x,y in zip(r,c)) for c in cols] for r in a]
def mv(a,v): return [sum(x*y for x,y in zip(r,v)) for r in a]
def inner(p,f,g): return sum(x*y*z for x,y,z in zip(p,f,g))
def energy(p,a,f): return inner(p,f,mv(a,f))
def psd(a):
    """Exact Schur elimination, including zero pivots. Input symmetric."""
    a=[r[:] for r in a];n=len(a)
    assert all(a[i][j]==a[j][i] for i in range(n) for j in range(n))
    for i in range(n):
        v=a[i][i]
        if v<0:return False
        if not v:
            if any(a[i][j] for j in range(i+1,n)):return False
            continue
        for j in range(i+1,n):
            for k in range(j,n):
                a[j][k]-=a[j][i]*a[i][k]/v;a[k][j]=a[j][k]
    return True
def weighted_form(p,a):return [[p[i]*v for v in r] for i,r in enumerate(a)]
def conditional(p,keys):
    groups=defaultdict(list)
    for i,k in enumerate(keys):groups[k].append(i)
    E=zero(len(p))
    for inds in groups.values():
        mass=sum(p[i] for i in inds)
        for i in inds:
            for j in inds:E[i][j]=p[j]/mass
    return E
def projection(p,z):
    z=[F(x)-sum(p[i]*z[i] for i in range(len(p))) for x in z]
    norm=inner(p,z,z)
    if not norm:return zero(len(p))
    return [[x*p[j]*z[j]/norm for j in range(len(p))] for x in z]
def law(ws):
    z=sum(ws);return [w/z for w in ws]
def graph_weight(g,w):return prod(w[e] for e in g)
def matchings(v):
    if not v:yield frozenset();return
    i=min(v)
    for j in sorted(v-{i}):
        for r in matchings(v-{i,j}):yield r|{edge(i,j)}
def graphs(n,d):
    es=list(combinations(range(n),2))
    for g in combinations(es,sum(d)//2):
        deg=Counter(v for e in g for v in e)
        if all(deg[i]==d[i] for i in range(n)):yield frozenset(g)
def fiber(g,a,n):
    i,j=a
    return (tuple(sorted(e for e in g if not set(e)&set(a))),a in g,
            tuple(int(edge(i,k) in g)+int(edge(j,k) in g) for k in range(n) if k not in a))
def switch(g,h):
    rem=g-h;ins=h-g
    return len(rem)==len(ins)==2 and len(set.union(*(set(e) for e in rem)))==4 and Counter(v for e in rem for v in e)==Counter(v for e in ins for v in e)

def slice_checks():
    cases=0;couplings=0
    t=F(101,100)
    for N in range(2,7):
      th=[t**((i%3)-1) for i in range(N)]
      for q in range(1,N):
        ss=[frozenset(s) for s in combinations(range(N),q)]
        ws=[prod(th[i] for i in s) for s in ss];p=law(ws);J=zero(len(ss))
        for i,s in enumerate(ss):
          for j,u in enumerate(ss):
            if len(s-u)==1:
              rate=min(F(1),ws[j]/ws[i]);J[i][j]=-rate;J[i][i]+=rate
        h=add(identity(len(ss)),scale(conditional(p,[0]*len(ss)),-1))
        assert psd(weighted_form(p,add(J,scale(h,-N*min(th)/max(th)))))
        cases+=1
        # Explicit generator coupling for every adjacent pair, no invocation of a spectral theorem.
        for s in ss:
          for u in ss:
            if len(s-u)!=1:continue
            i=next(iter(s-u));j=next(iter(u-s));C=s&u;V=set(range(N))-(s|u)
            events=[]
            def ev(a,b,r):
              if r:events.append((a,b,r))
            for k in C:
              for l in V:ev((s-{k})|{l},(u-{k})|{l},th[l])
            for l in V:ev((s-{i})|{l},(u-{j})|{l},th[l])
            ev((s-{i})|{j},u,th[j]);ev(s,(u-{j})|{i},th[i])
            for k in C:
              r=min(th[i],th[j]);ev((s-{k})|{j},(u-{k})|{i},r)
              ev((s-{k})|{j},u,th[j]-r);ev(s,(u-{k})|{i},th[i]-r)
            for side,start in [(0,s),(1,u)]:
              marg=defaultdict(F)
              for a,b,r in events:
                dest=(a,b)[side]
                if dest!=start:marg[frozenset(dest)]+=r
              expected={frozenset((start-{a})|{b}):th[b] for a in start for b in set(range(N))-start}
              assert dict(marg)==expected
            drift=sum(r*(len(a-b)-1) for a,b,r in events)
            assert drift<=-N*min(th)
            couplings+=1
    # N=3,q=1: weighted equality-indicator comparison fails for every t>1.
    p=law([t,F(1),F(1)]);S=zero(3);G=zero(3)
    for i,j in combinations(range(3),2):
        S=add(S,projection(p,[int(k not in (i,j)) for k in range(3)]))
        E=conditional(p,[0 if k in (i,j) else k+1 for k in range(3)])
        G=add(G,add(identity(3),scale(E,-1)))
    f=[F(1),F(0),F(0)];diff=energy(p,add(S,scale(G,-1)),f)
    assert diff==2*t*(t-1)/((t+1)*(t+2)**2)>0
    return {'slice_PSD_cases':cases,'coupling_marginal_and_drift_checks':couplings,'equality_comparison_violation':str(diff)}

def disjoint_checks():
    t=F(101,100)
    cells=[(0,0,1,1),(1,1,1,1),(2,2,2,2),(2,1,1,1),(1,2,2,2),(0,2,0,1)]
    checked=0
    for A,B,q0,q1 in cells:
        states=[];ws=[]
        cross=[t,1/t,F(1),t]
        for bits in product(range(2),repeat=4):
            if sum(bits)!=2:continue
            r=bits[0]+bits[1];c=bits[0]+bits[2]
            if not(0<=q0-r<=A and 0<=q1-c<=B):continue
            for U in combinations(range(A),q0-r):
              for V in combinations(range(B),q1-c):
                states.append((bits,r,c,U,V))
                ws.append(prod(cross[i] for i in range(4) if bits[i])*prod(t**(i+1) for i in U)*prod(t**(-i-1) for i in V))
        if not states:continue
        p=law(ws);N=len(p);I=identity(N)
        kx=[(c,V) for bits,r,c,U,V in states];ky=[(r,U) for bits,r,c,U,V in states]
        ha=add(I,scale(conditional(p,kx),-1));hb=add(I,scale(conditional(p,ky),-1))
        kg=[('center',U,V) if r==c==1 else ('single',i) for i,(bits,r,c,U,V) in enumerate(states)]
        g=add(I,scale(conditional(p,kg),-1))
        Ra=zero(N);Rb=zero(N)
        for keys,which,R in [(kx,1,Ra),(ky,2,Rb)]:
          groups=defaultdict(list)
          for i,k in enumerate(keys):groups[k].append(i)
          for inds in groups.values():
            # Equality error exists only when the opposite margin equals 1.
            if states[inds[0]][3-which]!=1:continue
            pp=law([p[i] for i in inds]);zz=[int(states[i][which]!=1) for i in inds];rr=projection(pp,zz)
            for ii,i in enumerate(inds):
              for jj,j in enumerate(inds):R[i][j]=rr[ii][jj]
        test=add(add(mul(ha,hb),mul(hb,ha)),add(scale(g,-2),add(Ra,Rb)))
        assert psd(weighted_form(p,test))
        checked+=1
    # A literal K6 degree-one cell with one cross-edge.
    states=[]
    for r,c in product(range(2),repeat=2):
        states.append(frozenset([edge(r,2+c),edge(1-r,4),edge(3-c,5)]))
    w={e:F(1) for e in combinations(range(6),2)};w[(0,2)]=w[(1,3)]=t
    p=law([graph_weight(g,w) for g in states]);I=identity(4)
    ha=add(I,scale(conditional(p,[fiber(g,(0,1),6) for g in states]),-1))
    hb=add(I,scale(conditional(p,[fiber(g,(2,3),6) for g in states]),-1))
    f=[F(2-2*r-2*c) for r,c in product(range(2),repeat=2)]
    interaction=2*inner(p,mv(ha,f),mv(hb,f));rho=(t-1)/(t+1)
    assert interaction==-2*rho*(1-rho*rho)<0
    return {'s2_exact_matrix_PSD_cases':checked,'s1_interaction':str(interaction),'rho':str(rho)}

def three_rows():
    t=F(101,100);states=[];ws=[]
    for U in product(range(3),repeat=2):
      for W in product(range(3),repeat=2):
        ku=tuple(U.count(i) for i in range(3));kw=tuple(W.count(i) for i in range(3))
        if ku!=kw:continue
        states.append((U,W,kw));ws.append(t**int(U[0] in (0,1)))
    counts=defaultdict(F);num=defaultdict(F)
    for (U,W,k),w in zip(states,ws):counts[k]+=w;num[k]+=w*int(U[0]==0)
    # Independent coefficient construction for the two partition polynomials.
    au=defaultdict(F);bw=defaultdict(F)
    for U in product(range(3),repeat=2):au[tuple(U.count(i) for i in range(3))]+=t**int(U[0] in (0,1))
    for W in product(range(3),repeat=2):bw[tuple(W.count(i) for i in range(3))]+=1
    assert all(counts[k]==au[k]*bw[k] for k in counts)
    m1=num[(1,1,0)]/counts[(1,1,0)];m2=num[(1,0,1)]/counts[(1,0,1)]
    assert m1==F(1,2) and m2==t/(t+1) and m1!=m2
    return {'states':len(states),'same_k1_conditional_means':[str(m1),str(m2)],'count_weights':{str(k):str(v) for k,v in counts.items()}}

def chain_checks():
    t=F(101,100);outputs=[]
    for n,d in [(4,[1]*4),(5,[1,2,1,1,1]),(6,[1]*6)]:
        ss=list(graphs(n,d));N=len(ss);w={e:t**((i%3)-1) for i,e in enumerate(combinations(range(n),2))};ws=[graph_weight(g,w) for g in ss];p=law(ws);I=identity(N);H=zero(N);hs={};Jsum=zero(N);L=zero(N)
        for i,g in enumerate(ss):
          for j,h in enumerate(ss):
            if switch(g,h):
                rate=min(F(1),ws[j]/ws[i]);L[i][j]=-rate;L[i][i]+=rate
        for a in combinations(range(n),2):
            keys=[fiber(g,a,n) for g in ss];E=conditional(p,keys);h=add(I,scale(E,-1));hs[a]=h;H=add(H,h)
            assert mul(E,E)==E
            assert all(p[i]*E[i][j]==p[j]*E[j][i] for i in range(N) for j in range(N))
            for i,g in enumerate(ss):
              for j,gg in enumerate(ss):
                if i!=j and keys[i]==keys[j] and switch(g,gg):
                    rate=min(F(1),ws[j]/ws[i]);Jsum[i][j]-=rate;Jsum[i][i]+=rate
        assert Jsum==scale(L,2)
        P=add(I,scale(L,-F(1,12*comb(n,4))))
        assert all(sum(r)==1 and r[i]>=F(1,2) for i,r in enumerate(P))
        assert all(p[i]*P[i][j]==p[j]*P[j][i] for i in range(N) for j in range(N))
        D=zero(N);triples=zero(N)
        for a,ha in hs.items():
          for b,hb in hs.items():
            if not set(a)&set(b):D=add(D,mul(ha,hb))
        for T in combinations(range(n),3):
            HT=zero(N)
            for a in combinations(T,2):HT=add(HT,hs[a])
            triples=add(triples,mul(HT,HT))
        assert mul(H,H)==add(add(triples,scale(H,-(n-3))),D)
        assert psd(weighted_form(p,add(scale(L,t**4),scale(H,-1))))
        # Gauge invariance, with positive rational vertex factors.
        factors=[F(i+2,i+1) for i in range(n)];wg={e:w[e]*factors[e[0]]*factors[e[1]] for e in w}
        assert law([graph_weight(g,wg) for g in ss])==p
        outputs.append({'n':n,'d':d,'states':N,'directed_switches':sum(switch(g,h) for g in ss for h in ss)})
    return outputs

def cycles(X,Y):
    adj=defaultdict(list)
    for u,v in X^Y:adj[u].append(v);adj[v].append(u)
    unseen=set(adj);out=[];mx={u:v for a,b in X for u,v in [(a,b),(b,a)]};my={u:v for a,b in Y for u,v in [(a,b),(b,a)]}
    while unseen:
        v0=min(unseen);vs=[v0];cur=v0;takeX=True
        while True:
            cur=(mx if takeX else my)[cur];takeX=not takeX
            if cur==v0:break
            vs.append(cur)
        unseen-=set(vs);out.append(vs)
    return out

def path(X,Y):
    Z=X
    for vs in cycles(X,Y):
        k=len(vs)//2
        for j in range(k-1):
            # Z is the state after j pivot switches on this cycle.
            E=Counter(X);E.update(Y);E.subtract(Z)
            if j==0:code=(0,vs[0],vs[1],0,0);FF={e for e,v in E.items() if v}
            else:
                a,p,b,c=vs[0],vs[2*j+1],vs[1],vs[2*j]
                code=(1,a,p,b,c);EE=E.copy();EE[edge(a,p)]+=1;EE[edge(a,b)]-=1;EE[edge(p,c)]-=1;EE[edge(b,c)]+=1
                assert set(EE.values())<={0,1};FF={e for e,v in EE.items() if v}
            new=(Z-{edge(vs[0],vs[2*j+1]),edge(vs[2*j+2],vs[2*j+3])})|{edge(vs[2*j+1],vs[2*j+2]),edge(vs[0],vs[2*j+3])}
            yield Z,frozenset(new),frozenset(FF),code,E
            Z=frozenset(new)
    assert Z==Y

def reconstruct(Z,FF,code):
    flag,a,p,b,c=code;E=Counter(FF)
    if flag:
        E[edge(a,p)]-=1;E[edge(a,b)]+=1;E[edge(p,c)]+=1;E[edge(b,c)]-=1;first=b
    else:first=p
    overlay=E.copy();overlay.update(Z)
    assert set(overlay.values())<={0,1,2}
    X={e for e,v in overlay.items() if v==2};Y=X.copy();adj=defaultdict(list)
    for (u,v),k in overlay.items():
        if k==1:adj[u].append(v);adj[v].append(u)
    unseen=set(adj)
    while unseen:
        v0=min(unseen);v1=first if v0==a else min(adj[v0]);vs=[v0,v1]
        while True:
            nxt=next(v for v in adj[vs[-1]] if v!=vs[-2])
            if nxt==v0:break
            vs.append(nxt)
        unseen-=set(vs)
        evens={edge(vs[i],vs[(i+1)%len(vs)]) for i in range(0,len(vs),2)}
        odds={edge(vs[i],vs[(i+1)%len(vs)]) for i in range(1,len(vs),2)}
        if v0==a:xe,ye=evens,odds
        elif v0<a:ye=evens if evens<=Z else odds;xe=odds if ye==evens else evens
        else:xe=evens if evens<=Z else odds;ye=odds if xe==evens else evens
        X|=xe;Y|=ye
    return frozenset(X),frozenset(Y)

def flow_checks(n=8):
    ss=list(matchings(set(range(n))));t=F(101,100);w={e:t**((i%3)-1) for i,e in enumerate(combinations(range(n),2))};W={g:graph_weight(g,w) for g in ss};ZZ=sum(W.values());p={g:W[g]/ZZ for g in ss};loads=defaultdict(F);seen={};incidences=0;maxdef=0
    for X in ss:
      for Y in ss:
        steps=list(path(X,Y));assert len(steps)<=n//2
        for Z,Zp,FF,code,E in steps:
            assert switch(Z,Zp) and FF in W
            assert reconstruct(Z,FF,code)==(X,Y)
            key=(Z,FF,code)
            assert key not in seen or seen[key]==(X,Y)
            seen[key]=(X,Y)
            EW=prod(w[e]**v for e,v in E.items())
            assert W[X]*W[Y]==W[Z]*EW and t**(-4)<=EW/W[FF]<=t**4
            maxdef=max(maxdef,sum(abs(E[e]-int(e in FF)) for e in w))
            loads[(Z,Zp)]+=p[X]*p[Y]*len(steps);incidences+=1
    denom=12*comb(n,4);rho=max(load/(min(p[Z],p[Zp])/denom) for (Z,Zp),load in loads.items())
    bound=2*(n//2)*n**4*denom*t**8
    assert rho<=bound
    return {'n':n,'states':len(ss),'ordered_demands':len(ss)**2,'path_incidences':incidences,'max_repair_l1':maxdef,'max_congestion':str(rho),'proved_upper_bound':str(bound),'all_endpoint_reconstructions':True}

def i19_check():
    ss=list(matchings(set(range(6))));cycle={edge(i,(i+1)%6) for i in range(6)};poly=Counter(len(g-cycle) for g in ss)
    assert dict(poly)=={0:2,1:3,2:6,3:4}
    for L in [1,2,7,20]:
        delta=F(1,2**L);w={e:F(1) if e in cycle else delta for e in combinations(range(6),2)}
        X=next(g for g in ss if g<=cycle)
        escape=sum(min(F(1),graph_weight(g,w)) for g in ss if switch(X,g))/180
        assert escape==(delta+delta**2)/60
    return {'partition_coefficients':dict(sorted(poly.items())),'exit_formula':'(delta+delta^2)/60','L_values':[1,2,7,20]}

def main():
    return {'slices':slice_checks(),'disjoint':disjoint_checks(),'three_rows':three_rows(),'chains':chain_checks(),'matching_flow':flow_checks(),'I19':i19_check(),'scope':'Exact finite algebra and incidence checks, not a proof of W or independent contribution review.'}
if __name__=='__main__':print(json.dumps(main(),indent=2,sort_keys=True))
